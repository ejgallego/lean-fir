import Fir.Wasm.Concrete.OwnershipFrameCorrectness
import Fir.Wasm.Concrete.ConstructorHeapCorrectness
import Fir.Wasm.Concrete.ReuseMemoryCorrectness

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
  concreteReset : resetObject before count address witness.closureDescriptors =
    .ok (after, address)
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

/-- Canonical semantic constructor installed when a nonempty reuse token is
consumed. The old tag is retained exactly when `updateHeader` is false; all
non-object payload is reset to the FIR runtime's zero/empty state. -/
def reusedConstructorObject (old : ConstructorObject) (info : LCNF.CtorInfo)
    (updateHeader : Bool) (fields : Array Value) : ConstructorObject := {
  tag := if updateHeader then info.cidx else old.tag
  objectFields := fields
  usizeFields := Array.replicate info.usize 0
  scalarFields := [] }

/-- The complete in-place byte transaction reconstructs a normal constructor
decoder relation under the replacement descriptor. The active layout may be
smaller than the retained allocation; every replacement `USize` byte is read
from the scrubbed payload, while object fields come from the exact field-write
postcondition. -/
theorem ConstructorObjectRel.ofReuseConstructorMemory
    (state : MemoryState) (memory scrubbed fieldMemory : LinearMemory)
    (witness : RefinementWitness) (address : Word32)
    (oldInfo : LCNF.CtorInfo) (oldFieldKinds : Array AbiKind)
    (old : ConstructorObject) (info : LCNF.CtorInfo)
    (fieldKinds : Array AbiKind) (fields : Array Word32)
    (semanticFields : Array Value) (updateHeader : Bool)
    (header replacement : Header)
    (related : ConstructorObjectRel state witness address oldInfo oldFieldKinds old)
    (headerRead : state.readLiveHeader address = .ok header)
    (retainedExtent : address.value + header.allocationBytes.toNat ≤
      state.heapCursor)
    (replacementKind : replacement.kind = .constructor)
    (replacementLive : replacement.live = true)
    (replacementAllocation : replacement.allocationBytes = header.allocationBytes)
    (replacementTag : replacement.aux0.toNat =
      if updateHeader then info.cidx else old.tag)
    (replacementObjectFields : replacement.aux1.toNat = info.size)
    (replacementUSizeFields : replacement.aux2.toNat = info.usize)
    (replacementScalarBytes : replacement.aux3.toNat = info.ssize)
    (layoutFits : (ConstructorLayout.ofInfo info).allocationBytes ≤
      header.allocationBytes.toNat)
    (arity : fields.size = info.size)
    (semanticArity : semanticFields.size = info.size)
    (fieldKindsSize : fieldKinds.size = info.size)
    (fieldKindsValid : fieldKinds.all AbiKind.isObjectField = true)
    (fieldRelated : ∀ (index : Nat) (kind : AbiKind) (value : Value),
      fieldKinds[index]? = some kind →
      semanticFields[index]? = some value →
      ∃ word, fields[index]? = some word ∧
        ValueRel witness kind (.word32 word) value)
    (post : ReuseConstructorMemoryPost state.memory scrubbed fieldMemory memory
      address header.allocationBytes.toNat replacement fields.toList) :
    ConstructorObjectRel ({ state with memory } : MemoryState)
      (witness.rebindConstructor address info fieldKinds) address info fieldKinds
      (reusedConstructorObject old info updateHeader semanticFields) := by
  obtain ⟨addressHeap, _, _, headerMinimum, headerAligned, headerInBounds⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead
  have finalHeader :
      ({ state with memory } : MemoryState).readLiveHeader address =
        .ok replacement := by
    unfold MemoryState.readLiveHeader
    rw [addressHeap, post.headerRead]
    simp only [Bind.bind, Except.bind]
    rw [if_pos replacementLive]
    have replacementMinimum : headerBytes ≤ replacement.allocationBytes.toNat := by
      rw [replacementAllocation]
      exact headerMinimum
    have replacementAligned :
        replacement.allocationBytes.toNat % target.heapAlignment = 0 := by
      rw [replacementAllocation]
      exact headerAligned
    have replacementInBounds :
        address.value + replacement.allocationBytes.toNat ≤ memory.size := by
      rw [replacementAllocation, post.size]
      exact headerInBounds
    have checks :
        (decide (headerBytes ≤ replacement.allocationBytes.toNat) &&
          decide (replacement.allocationBytes.toNat % target.heapAlignment = 0) &&
          decide (address.value + replacement.allocationBytes.toNat ≤ memory.size)) =
            true := by
      simp [replacementMinimum, replacementAligned, replacementInBounds]
    rw [if_pos checks]
    rfl
  have headerWriteInBounds : address.value + headerBytes ≤ fieldMemory.size := by
    rw [post.fieldPost.size, post.scrubPost.size]
    exact Nat.le_trans (Nat.add_le_add_left headerMinimum address.value)
      headerInBounds
  have constructorHeader :
      readConstructorHeader ({ state with memory } : MemoryState) address =
        .ok replacement := by
    have kindCheck : (replacement.kind == ObjectKind.constructor) = true := by
      rw [replacementKind]
      decide
    unfold readConstructorHeader
    rw [addressHeap, finalHeader]
    simp only [Bind.bind, Except.bind, liftMemory]
    rw [if_pos kindCheck]
    rfl
  refine {
    header := ⟨replacement, finalHeader, replacementKind, ?_,
      replacementTag, replacementObjectFields,
      replacementUSizeFields, replacementScalarBytes⟩
    headerOwned := related.headerOwned
    extent := ?_
    semanticObjectFields := by simpa [reusedConstructorObject] using semanticArity
    semanticUSizeFields := by simp [reusedConstructorObject]
    semanticScalarFields := by simp [reusedConstructorObject]
    fieldKindsSize
    fieldKindsValid
    objectFields := ?_
    usizeFields := ?_ }
  · simpa [replacementAllocation] using layoutFits
  · exact Nat.le_trans (Nat.add_le_add_left layoutFits address.value) retainedExtent
  · intro index kind value kindAt valueAt
    have semanticAt : semanticFields[index]? = some value := by
      simpa [reusedConstructorObject] using valueAt
    obtain ⟨word, wordAt, valueRelated⟩ :=
      fieldRelated index kind value kindAt semanticAt
    have indexLt : index < info.size := by
      obtain ⟨indexLtFields, _⟩ := Array.getElem?_eq_some_iff.mp wordAt
      omega
    have listAt : fields.toList[index]? = some word := by simpa using wordAt
    have fieldRead := post.fieldAt index word listAt
    have paddingRead := post.paddingAt index word listAt
    have concreteRead :
        readObjectField ({ state with memory } : MemoryState) address index =
          .ok word := by
      have exactField : memory.readWord32
          (address.value + headerBytes + target.semanticSlotBytes * index) =
          .ok word := by
        simpa [objectFieldAddress] using fieldRead
      have exactPadding : memory.readUInt32
          (address.value + headerBytes + target.semanticSlotBytes * index + 4) =
          .ok 0 := by
        simpa [objectFieldAddress] using paddingRead
      unfold readObjectField
      rw [constructorHeader]
      simp only [Bind.bind, Except.bind]
      simp [replacementObjectFields, indexLt, exactField, exactPadding, liftMemory]
      rfl
    exact ⟨word, concreteRead,
      valueRelated.rebindConstructor address info fieldKinds⟩
  · intro index value valueAt
    change (Array.replicate info.usize (0 : UInt64))[index]? = some value at valueAt
    rw [Array.getElem?_replicate] at valueAt
    have indexLt : index < info.usize := by
      by_cases inBounds : index < info.usize
      · exact inBounds
      · rw [if_neg inBounds] at valueAt
        contradiction
    rw [if_pos indexLt] at valueAt
    have valueZero : value = 0 := Option.some.inj valueAt.symm
    subst value
    let offset := address.value + headerBytes +
      target.semanticSlotBytes * (info.size + index)
    have zeroBytes : ∀ byteOffset, byteOffset < 8 →
        memory[offset + byteOffset]? = some 0 := by
      intro byteOffset byteOffsetLt
      have afterFields : objectFieldAddress address.value fields.toList.length ≤
          offset + byteOffset := by
        simp [offset, objectFieldAddress, arity, target]
        omega
      have withinRetained :
          target.semanticSlotBytes * (info.size + index) + byteOffset <
            header.allocationBytes.toNat - headerBytes := by
        have aligned := align8_ge
          (headerBytes + target.semanticSlotBytes * (info.size + info.usize) +
            info.ssize)
        have beforeLayout :
            headerBytes + target.semanticSlotBytes * (info.size + index) +
                byteOffset < (ConstructorLayout.ofInfo info).allocationBytes := by
          simp [ConstructorLayout.ofInfo, target] at aligned ⊢
          omega
        have beforeAllocation :
            headerBytes + target.semanticSlotBytes * (info.size + index) +
                byteOffset < header.allocationBytes.toNat :=
          Nat.lt_of_lt_of_le beforeLayout layoutFits
        omega
      have scrubRead := post.scrubPost.zeroAt
        (target.semanticSlotBytes * (info.size + index) + byteOffset)
        withinRetained
      have fieldRead : fieldMemory.readByte (offset + byteOffset) = .ok 0 := by
        rw [post.fieldPost.byteFrame (offset + byteOffset) (.inr (by
          simpa only [Nat.zero_add] using afterFields))]
        simpa [offset, Nat.add_assoc] using scrubRead
      have finalRead : memory.readByte (offset + byteOffset) = .ok 0 := by
        have payloadStart : address.value + headerBytes ≤ offset + byteOffset := by
          simp [offset]
          omega
        rw [Header.readByte_of_write_eq_ok_other fieldMemory memory address
          replacement (offset + byteOffset) headerWriteInBounds post.headerWrite
          (.inr payloadStart)]
        exact fieldRead
      unfold LinearMemory.readByte at finalRead
      cases byte : memory[offset + byteOffset]? with
      | none => simp [byte] at finalRead
      | some actual =>
          simp [byte] at finalRead
          subst actual
          rfl
    have usizeRead : memory.readUInt64 offset = .ok 0 :=
      LinearMemory.readUInt64_of_zero_bytes memory offset zeroBytes
    unfold readUSizeField
    rw [constructorHeader]
    simp only [Bind.bind, Except.bind]
    simp [replacementObjectFields, replacementUSizeFields, indexLt, offset,
      usizeRead, liftMemory]

/-- The complete in-place transaction frames every byte of a disjoint
allocation. Unlike the unpublished scrub and field-write steps, this theorem
uses the final transaction postcondition directly. -/
theorem MemoryState.AllocationFrame.ofReuseConstructorMemoryPost
    {before after : MemoryState} {targetAddress otherAddress : Word32}
    {targetBytes otherBytes : Nat} {scrubbed fieldMemory memory : LinearMemory}
    {replacement : Header} {fields : List Word32}
    (resultEq : after = { before with memory })
    (post : ReuseConstructorMemoryPost before.memory scrubbed fieldMemory memory
      targetAddress targetBytes replacement fields)
    (disjoint : targetAddress.value + targetBytes ≤ otherAddress.value ∨
      otherAddress.value + otherBytes ≤ targetAddress.value) :
    before.AllocationFrame after otherAddress otherBytes := by
  subst after
  refine ⟨rfl, post.size, ?_⟩
  intro offset offsetLt
  apply post.frame
  cases disjoint with
  | inl targetBefore => right; omega
  | inr otherBefore => left; omega

/-- The global descriptor invariant supplies the disjointness needed to frame
one non-target allocation through the complete in-place reuse transaction. -/
theorem LiveHeapRel.allocationFrame_of_reuseConstructorMemory_other
    {before after : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {targetAddress otherAddress : Word32}
    {targetDescriptor otherDescriptor : AllocationDescriptor}
    {targetHeader otherHeader replacement : Header}
    {scrubbed fieldMemory memory : LinearMemory} {fields : List Word32}
    (related : LiveHeapRel before witness runtime)
    (targetFound : witness.descriptors.lookup? targetAddress =
      some targetDescriptor)
    (otherFound : witness.descriptors.lookup? otherAddress =
      some otherDescriptor)
    (different : targetAddress.value ≠ otherAddress.value)
    (targetRead : Header.read before.memory targetAddress = .ok targetHeader)
    (otherRead : Header.read before.memory otherAddress = .ok otherHeader)
    (resultEq : after = { before with memory })
    (post : ReuseConstructorMemoryPost before.memory scrubbed fieldMemory memory
      targetAddress targetHeader.allocationBytes.toNat replacement fields) :
    before.AllocationFrame after otherAddress
      otherHeader.allocationBytes.toNat := by
  obtain ⟨regionHeader, regionRead, _, _, _⟩ :=
    related.descriptorRegion targetAddress targetDescriptor targetFound
  rw [targetRead] at regionRead
  have headerEq := Except.ok.inj regionRead
  subst regionHeader
  have disjoint := related.descriptorDisjoint targetAddress otherAddress
    targetDescriptor otherDescriptor targetFound otherFound different targetHeader
      otherHeader targetRead otherRead
  exact .ofReuseConstructorMemoryPost resultEq post disjoint

/-- An in-place constructor transaction preserves the retained extent of
every previously mapped location. The target keeps its allocation word, while
descriptor disjointness frames every other mapped allocation. -/
theorem LiveHeapRel.mappedHeaderCapacity_of_reuseConstructorMemory
    {before after : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {targetAddress : Word32}
    {targetDescriptor : AllocationDescriptor} {targetHeader replacement : Header}
    {scrubbed fieldMemory memory : LinearMemory} {fields : List Word32}
    (related : LiveHeapRel before witness runtime)
    (targetFound :
      witness.descriptors.lookup? targetAddress = some targetDescriptor)
    (targetRead : Header.read before.memory targetAddress = .ok targetHeader)
    (resultEq : after = { before with memory })
    (post : ReuseConstructorMemoryPost before.memory scrubbed fieldMemory memory
      targetAddress targetHeader.allocationBytes.toNat replacement fields)
    (sameExtent : replacement.allocationBytes = targetHeader.allocationBytes) :
    MappedHeaderCapacityTransport before after witness := by
  intro address location header mapped headerRead headerOwned
  obtain ⟨cell, _, cellRelated⟩ :=
    related.concreteToSemantic location address mapped
  obtain ⟨descriptor, descriptorFound⟩ := cellRelated.descriptor
  by_cases different : targetAddress.value ≠ address.value
  · obtain ⟨regionHeader, regionRead, minimum, _, _⟩ :=
      related.descriptorRegion address descriptor descriptorFound
    rw [headerRead] at regionRead
    have regionHeaderEq := Except.ok.inj regionRead
    subst regionHeader
    have frame := related.allocationFrame_of_reuseConstructorMemory_other
      targetFound descriptorFound different targetRead headerRead resultEq post
    refine ⟨header, ?_, rfl, ?_⟩
    · rw [frame.readHeader minimum]
      exact headerRead
    · rw [frame.cursor]
      exact headerOwned
  · have sameValue : targetAddress.value = address.value := by omega
    have sameAddress : targetAddress = address := by
      cases targetAddress
      cases address
      simp_all
    subst address
    rw [targetRead] at headerRead
    have headerEq := Except.ok.inj headerRead
    subst header
    refine ⟨replacement, ?_, sameExtent, ?_⟩
    · rw [resultEq]
      exact post.headerRead
    · simpa [resultEq] using headerOwned

/-- Publishing a replacement header with the same retained extent preserves
all descriptor regions and pairwise disjointness while rebinding the target's
active constructor descriptor. -/
theorem LiveHeapRel.descriptorSpatial_of_reuseConstructorMemory
    {before after : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {targetAddress : Word32}
    {targetDescriptor : AllocationDescriptor} {targetHeader replacement : Header}
    {scrubbed fieldMemory memory : LinearMemory} {fields : List Word32}
    (newInfo : LCNF.CtorInfo) (newFieldKinds : Array AbiKind)
    (related : LiveHeapRel before witness runtime)
    (targetFound : witness.descriptors.lookup? targetAddress = some targetDescriptor)
    (targetRead : Header.read before.memory targetAddress = .ok targetHeader)
    (resultEq : after = { before with memory })
    (post : ReuseConstructorMemoryPost before.memory scrubbed fieldMemory memory
      targetAddress targetHeader.allocationBytes.toNat replacement fields)
    (sameExtent : replacement.allocationBytes = targetHeader.allocationBytes) :
    (∀ address descriptor,
      (witness.rebindConstructor targetAddress newInfo newFieldKinds).descriptors.lookup?
          address = some descriptor →
      ∃ header,
        Header.read after.memory address = .ok header ∧
        headerBytes ≤ header.allocationBytes.toNat ∧
        header.allocationBytes.toNat % target.heapAlignment = 0 ∧
        address.value + header.allocationBytes.toNat ≤ after.heapCursor) ∧
    (∀ left right leftDescriptor rightDescriptor,
      (witness.rebindConstructor targetAddress newInfo newFieldKinds).descriptors.lookup?
          left = some leftDescriptor →
      (witness.rebindConstructor targetAddress newInfo newFieldKinds).descriptors.lookup?
          right = some rightDescriptor →
      left.value ≠ right.value →
      ∀ leftHeader rightHeader,
        Header.read after.memory left = .ok leftHeader →
        Header.read after.memory right = .ok rightHeader →
        left.value + leftHeader.allocationBytes.toNat ≤ right.value ∨
          right.value + rightHeader.allocationBytes.toNat ≤ left.value) := by
  have wordEq : ∀ left right : Word32, left.value = right.value → left = right := by
    intro left right equal
    cases left
    cases right
    simp_all
  obtain ⟨regionHeader, regionRead, targetMinimum, targetAligned, targetExtent⟩ :=
    related.descriptorRegion targetAddress targetDescriptor targetFound
  rw [targetRead] at regionRead
  have regionHeaderEq := Except.ok.inj regionRead
  subst regionHeader
  have targetReadAfter : Header.read after.memory targetAddress = .ok replacement := by
    rw [resultEq]
    exact post.headerRead
  have replacementMinimum : headerBytes ≤ replacement.allocationBytes.toNat := by
    rw [sameExtent]
    exact targetMinimum
  have replacementAligned :
      replacement.allocationBytes.toNat % target.heapAlignment = 0 := by
    rw [sameExtent]
    exact targetAligned
  have replacementExtent :
      targetAddress.value + replacement.allocationBytes.toNat ≤ after.heapCursor := by
    rw [sameExtent, resultEq]
    exact targetExtent
  refine ⟨?_, ?_⟩
  · intro address descriptor found
    by_cases different : targetAddress.value ≠ address.value
    · rw [witness.lookup_rebindConstructor_descriptor_other targetAddress address
        newInfo newFieldKinds different] at found
      obtain ⟨header, headerRead, minimum, aligned, extent⟩ :=
        related.descriptorRegion address descriptor found
      have frame := related.allocationFrame_of_reuseConstructorMemory_other
        targetFound found different targetRead headerRead resultEq post
      exact ⟨header, by rw [frame.readHeader minimum]; exact headerRead,
        minimum, aligned, by rw [frame.cursor]; exact extent⟩
    · have sameValue : targetAddress.value = address.value := by omega
      have addressEq : address = targetAddress :=
        wordEq address targetAddress sameValue.symm
      subst address
      exact ⟨replacement, targetReadAfter, replacementMinimum,
        replacementAligned, replacementExtent⟩
  · intro left right leftDescriptor rightDescriptor leftFound rightFound different
      leftHeader rightHeader leftRead rightRead
    by_cases leftTarget : targetAddress.value = left.value
    · have rightTarget : targetAddress.value ≠ right.value := by
        intro rightEq
        exact different (leftTarget.symm.trans rightEq)
      have leftEq : left = targetAddress := wordEq left targetAddress leftTarget.symm
      subst left
      rw [targetReadAfter] at leftRead
      have leftHeaderEq := Except.ok.inj leftRead
      subst leftHeader
      rw [witness.lookup_rebindConstructor_descriptor_other targetAddress right
        newInfo newFieldKinds rightTarget] at rightFound
      obtain ⟨oldRightHeader, oldRightRead, rightMinimum, _, _⟩ :=
        related.descriptorRegion right rightDescriptor rightFound
      have frame := related.allocationFrame_of_reuseConstructorMemory_other
        targetFound rightFound rightTarget targetRead oldRightRead resultEq post
      rw [frame.readHeader rightMinimum] at rightRead
      simpa [sameExtent] using related.descriptorDisjoint targetAddress right
        targetDescriptor rightDescriptor targetFound rightFound rightTarget targetHeader
          rightHeader targetRead rightRead
    · by_cases rightTarget : targetAddress.value = right.value
      · have rightEq : right = targetAddress :=
          wordEq right targetAddress rightTarget.symm
        subst right
        rw [targetReadAfter] at rightRead
        have rightHeaderEq := Except.ok.inj rightRead
        subst rightHeader
        rw [witness.lookup_rebindConstructor_descriptor_other targetAddress left
          newInfo newFieldKinds leftTarget] at leftFound
        obtain ⟨oldLeftHeader, oldLeftRead, leftMinimum, _, _⟩ :=
          related.descriptorRegion left leftDescriptor leftFound
        have frame := related.allocationFrame_of_reuseConstructorMemory_other
          targetFound leftFound leftTarget targetRead oldLeftRead resultEq post
        rw [frame.readHeader leftMinimum] at leftRead
        simpa [sameExtent] using related.descriptorDisjoint left targetAddress
          leftDescriptor targetDescriptor leftFound targetFound (Ne.symm leftTarget)
            leftHeader targetHeader leftRead targetRead
      · rw [witness.lookup_rebindConstructor_descriptor_other targetAddress left
          newInfo newFieldKinds leftTarget] at leftFound
        rw [witness.lookup_rebindConstructor_descriptor_other targetAddress right
          newInfo newFieldKinds rightTarget] at rightFound
        obtain ⟨oldLeftHeader, oldLeftRead, leftMinimum, _, _⟩ :=
          related.descriptorRegion left leftDescriptor leftFound
        obtain ⟨oldRightHeader, oldRightRead, rightMinimum, _, _⟩ :=
          related.descriptorRegion right rightDescriptor rightFound
        have leftFrame := related.allocationFrame_of_reuseConstructorMemory_other
          targetFound leftFound leftTarget targetRead oldLeftRead resultEq post
        have rightFrame := related.allocationFrame_of_reuseConstructorMemory_other
          targetFound rightFound rightTarget targetRead oldRightRead resultEq post
        rw [leftFrame.readHeader leftMinimum] at leftRead
        rw [rightFrame.readHeader rightMinimum] at rightRead
        exact related.descriptorDisjoint left right leftDescriptor rightDescriptor
          leftFound rightFound different leftHeader rightHeader leftRead rightRead

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
  let header := related.header.choose
  obtain ⟨headerRead, headerKind, allocationBytes,
      tag, objectCount, usizeCount, scalarCount⟩ := related.header.choose_spec
  change state.readLiveHeader address = .ok header at headerRead
  change header.kind = .constructor at headerKind
  change (ConstructorLayout.ofInfo info).allocationBytes ≤
    header.allocationBytes.toNat at allocationBytes
  change header.aux0.toNat = semantic.tag at tag
  change header.aux1.toNat = info.size at objectCount
  change header.aux2.toNat = info.usize at usizeCount
  change header.aux3.toNat = info.ssize at scalarCount
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
    header := ⟨header, headerAfter, headerKind, allocationBytes,
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

/-- Rebinding a distinct active constructor descriptor preserves a closure's
immutable module tables, metadata decoder, and typed captures. -/
theorem ClosureObjectRel.rebindConstructor_other
    {state : MemoryState} {witness : RefinementWitness}
    {address reboundAddress : Word32} {function : Lean.Name} {arity : Nat}
    {captureKinds : Array AbiKind} {captures : Array Value}
    {reboundInfo : LCNF.CtorInfo} {reboundFieldKinds : Array AbiKind}
    (related : ClosureObjectRel state witness witness.closureDispatch
      witness.closureDescriptors address function arity captureKinds captures)
    (different : reboundAddress.value ≠ address.value) :
    ClosureObjectRel state
      (witness.rebindConstructor reboundAddress reboundInfo reboundFieldKinds)
      (witness.rebindConstructor reboundAddress reboundInfo reboundFieldKinds).closureDispatch
      (witness.rebindConstructor reboundAddress reboundInfo reboundFieldKinds).closureDescriptors
      address function arity captureKinds captures := by
  refine {
    descriptor := ?_
    metadata := related.metadata
    captureKindsSize := related.captureKindsSize
    captures := ?_ }
  · rw [witness.lookup_rebindConstructor_descriptor_other reboundAddress address
      reboundInfo reboundFieldKinds different]
    exact related.descriptor
  · intro index kind value kindAt valueAt
    obtain ⟨lane, read, laneRelated⟩ :=
      related.captures index kind value kindAt valueAt
    exact ⟨lane, read,
      laneRelated.rebindConstructor reboundAddress reboundInfo reboundFieldKinds⟩

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
  | natural descriptor objectEq headerRead headerKind marker extent limbsFit
      decoded refCount persistent live =>
      exact .natural
        (by
          rw [witness.lookup_rebindConstructor_descriptor_other reboundAddress
            address reboundInfo reboundFieldKinds different]
          exact descriptor)
        objectEq headerRead headerKind marker extent limbsFit decoded refCount
          persistent live
  | integer descriptor objectEq objectRelated refCount persistent live =>
      exact .integer
        (by
          rw [witness.lookup_rebindConstructor_descriptor_other reboundAddress
            address reboundInfo reboundFieldKinds different]
          exact descriptor)
        objectEq objectRelated refCount persistent live
  | string descriptor objectEq objectRelated refCount persistent live =>
      exact .string
        (by
          rw [witness.lookup_rebindConstructor_descriptor_other reboundAddress
            address reboundInfo reboundFieldKinds different]
          exact descriptor)
        objectEq objectRelated refCount persistent live
  | closure closureRelated =>
      cases closureRelated with
      | closure objectEq objectRelated headerRead headerKind descriptorLookup
          fixedCount extent refCount persistent live =>
          exact .closure (.closure objectEq
            (objectRelated.rebindConstructor_other different) headerRead headerKind
            descriptorLookup fixedCount extent refCount persistent live)

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

/-- A complete in-place transaction and matching semantic cell replacement
restore the normal whole-heap relation under the replacement constructor
descriptor. -/
theorem LiveHeapRel.setCell_ofReuseConstructorMemory
    (state : MemoryState) (memory scrubbed fieldMemory : LinearMemory)
    (witness : RefinementWitness) (runtime : RuntimeState)
    (location : Location) (address : Word32) (cell : HeapCell)
    (oldInfo : LCNF.CtorInfo) (oldFieldKinds : Array AbiKind)
    (old : ConstructorObject) (info : LCNF.CtorInfo)
    (fieldKinds : Array AbiKind) (fields : Array Word32)
    (semanticFields : Array Value) (updateHeader : Bool)
    (header replacement : Header)
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (descriptor : witness.descriptors.lookup? address =
      some (.constructor oldInfo oldFieldKinds))
    (_objectEq : cell.object = .ctor old)
    (objectRelated : ConstructorObjectRel state witness address oldInfo
      oldFieldKinds old)
    (headerRead : state.readLiveHeader address = .ok header)
    (_headerKind : header.kind = .constructor)
    (refCount : header.refCount.toNat = cell.rc)
    (persistent : header.persistent = cell.persistent)
    (ordinary : cell.persistent = false)
    (cellLive : cell.live = true)
    (replacementKind : replacement.kind = .constructor)
    (replacementLive : replacement.live = true)
    (replacementPersistent : replacement.persistent = false)
    (replacementRefCount : replacement.refCount = header.refCount)
    (replacementAllocation : replacement.allocationBytes = header.allocationBytes)
    (replacementTag : replacement.aux0.toNat =
      if updateHeader then info.cidx else old.tag)
    (replacementObjectFields : replacement.aux1.toNat = info.size)
    (replacementUSizeFields : replacement.aux2.toNat = info.usize)
    (replacementScalarBytes : replacement.aux3.toNat = info.ssize)
    (layoutFits : (ConstructorLayout.ofInfo info).allocationBytes ≤
      header.allocationBytes.toNat)
    (arity : fields.size = info.size)
    (semanticArity : semanticFields.size = info.size)
    (fieldKindsSize : fieldKinds.size = info.size)
    (fieldKindsValid : fieldKinds.all AbiKind.isObjectField = true)
    (fieldRelated : ∀ (index : Nat) (kind : AbiKind) (value : Value),
      fieldKinds[index]? = some kind →
      semanticFields[index]? = some value →
      ∃ word, fields[index]? = some word ∧
        ValueRel witness kind (.word32 word) value)
    (written : state.memory.reuseConstructorMemory address
      header.allocationBytes.toNat replacement fields.toList = .ok memory)
    (post : ReuseConstructorMemoryPost state.memory scrubbed fieldMemory memory
      address header.allocationBytes.toNat replacement fields.toList) :
    let semanticObject :=
      reusedConstructorObject old info updateHeader semanticFields
    let semanticCell : HeapCell := { cell with object := .ctor semanticObject }
    ∃ nextRuntime,
      setCell runtime location semanticCell = .ok nextRuntime ∧
      LiveHeapRel ({ state with memory } : MemoryState)
        (witness.rebindConstructor address info fieldKinds) nextRuntime := by
  dsimp only
  obtain ⟨addressHeap, rawHeaderRead, _, headerMinimum, headerAligned,
      headerInBounds⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead
  obtain ⟨regionHeader, regionRead, _, _, retainedExtent⟩ :=
    related.descriptorRegion address (.constructor oldInfo oldFieldKinds) descriptor
  rw [rawHeaderRead] at regionRead
  have regionHeaderEq := Except.ok.inj regionRead
  subst regionHeader
  have fieldsInAllocation : objectFieldAddress address.value fields.toList.length ≤
      address.value + header.allocationBytes.toNat := by
    have aligned := align8_ge
      (headerBytes + target.semanticSlotBytes * (info.size + info.usize) + info.ssize)
    simp [ConstructorLayout.ofInfo, target] at aligned layoutFits
    simp [objectFieldAddress, arity, target]
    omega
  have finalFrontier :
      ({ state with memory } : MemoryState).FrontierInvariant :=
    related.frontier.reuseConstructorMemory headerMinimum retainedExtent
      fieldsInAllocation written
  have targetObjectRelated := objectRelated.ofReuseConstructorMemory state memory
    scrubbed fieldMemory witness address oldInfo oldFieldKinds old info fieldKinds
      fields semanticFields updateHeader header replacement headerRead retainedExtent
      replacementKind replacementLive replacementAllocation
      replacementTag replacementObjectFields replacementUSizeFields
      replacementScalarBytes layoutFits arity semanticArity fieldKindsSize
      fieldKindsValid fieldRelated post
  have finalHeader :
      ({ state with memory } : MemoryState).readLiveHeader address =
        .ok replacement := by
    unfold MemoryState.readLiveHeader
    rw [addressHeap, post.headerRead]
    simp only [Bind.bind, Except.bind]
    rw [if_pos replacementLive]
    have checks :
        (decide (headerBytes ≤ replacement.allocationBytes.toNat) &&
          decide (replacement.allocationBytes.toNat % target.heapAlignment = 0) &&
          decide (address.value + replacement.allocationBytes.toNat ≤ memory.size)) =
            true := by
      rw [replacementAllocation, post.size]
      simp [headerMinimum, headerAligned, headerInBounds]
    rw [if_pos checks]
    rfl
  have targetAfter : CellRel ({ state with memory } : MemoryState)
      (witness.rebindConstructor address info fieldKinds) address
      { cell with object := HeapObject.ctor (reusedConstructorObject old info
          updateHeader semanticFields) } := by
    apply CellRel.live
    apply LiveCellRel.constructor
      (witness.lookup_rebindConstructor_descriptor address info fieldKinds)
      rfl targetObjectRelated finalHeader replacementKind
    · rw [replacementRefCount]
      exact refCount
    · exact replacementPersistent.trans ordinary.symm
    · simpa using cellLive
  obtain ⟨descriptorRegion, descriptorDisjoint⟩ :=
    related.descriptorSpatial_of_reuseConstructorMemory info fieldKinds descriptor
      rawHeaderRead rfl post replacementAllocation
  have cellFrame : ∀ other otherAddress otherCell,
      other ≠ location →
      findCell? runtime.heap other = some otherCell →
      witness.locations.lookup? other = some otherAddress →
      CellRel state witness otherAddress otherCell →
      CellRel ({ state with memory } : MemoryState)
        (witness.rebindConstructor address info fieldKinds) otherAddress otherCell := by
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
      apply differentWord
      cases address
      cases otherAddress
      simp_all
    have frame := related.allocationFrame_of_reuseConstructorMemory_other descriptor
      otherDescriptorFound differentValue rawHeaderRead otherHeaderRead rfl post
    exact (otherRelated.allocationFrame otherHeaderRead frame)
      |>.rebindConstructor_other differentValue
  have promotedFrame : ∀ payload other,
      witness.promotedTags.Contains payload other →
      PromotedTagRel ({ state with memory } : MemoryState)
        (witness.rebindConstructor address info fieldKinds) payload other := by
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
      apply differentWord
      cases address
      cases other
      simp_all
    have frame := related.allocationFrame_of_reuseConstructorMemory_other descriptor
      promoted.descriptor differentValue rawHeaderRead promotedRawRead rfl post
    exact (promoted.allocationFrame promotedHeaderRead frame)
      |>.rebindConstructor_other differentValue
  exact related.setCell_rebindConstructor_of_frames info fieldKinds mapped found rfl
    finalFrontier targetAfter descriptorRegion descriptorDisjoint cellFrame
      promotedFrame

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
        nextRuntime ∧
      MappedHeaderCapacityTransport state
        ({ state with memory } : MemoryState) witness := by
  have wordEq : ∀ left right : Word32, left.value = right.value → left = right := by
    intro left right equal
    cases left
    cases right
    simp_all
  have targetBefore : LiveCellRel state witness address cell :=
    .constructor descriptor objectEq objectRelated headerRead headerKind refCount
      persistent live
  let relationHeader := objectRelated.header.choose
  obtain ⟨relationRead, _, activeFits, _, _, _, _⟩ :=
    objectRelated.header.choose_spec
  change state.readLiveHeader address = .ok relationHeader at relationRead
  change (ConstructorLayout.ofInfo info).allocationBytes ≤
    relationHeader.allocationBytes.toNat at activeFits
  rw [headerRead] at relationRead
  have relationHeaderEq := Except.ok.inj relationRead
  rw [← relationHeaderEq] at activeFits
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
  obtain ⟨nextRuntime, semanticSet, finalRelated⟩ :=
    related.setCell_rebindConstructor_of_frames
      (result := ({ state with memory } : MemoryState)) info
      (resetProtocolFieldKinds fieldKinds count) mapped found rfl finalFrontier
        targetAfter protocolDescriptorRegion protocolDescriptorDisjoint cellFrame
          promotedFrame
  have capacity :=
    related.mappedHeaderCapacity_of_writeObjectFields descriptor rawRead rfl
      fieldsInTarget written
  exact ⟨nextRuntime, semanticSet, finalRelated, capacity⟩

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
      Fir.LeanIR.Impure.releaseResetField next value) = .ok finalRuntime) :
    ∃ finalState,
      words.foldlM (init := state) (fun next child =>
        decrementReferenceOnce next child true witness.closureDescriptors) =
          .ok finalState ∧
      LiveHeapRel finalState witness finalRuntime ∧
      MappedHeaderCapacityTransport state finalState witness := by
  induction related generalizing state runtime finalRuntime with
  | nil =>
      simp only [List.foldlM_nil] at semanticOperation ⊢
      have runtimeEq := Except.ok.inj semanticOperation
      subst finalRuntime
      exact ⟨state, rfl, heap, .refl state witness⟩
  | @cons word value words values head tail ih =>
      simp only [List.foldlM_cons, Bind.bind, Except.bind] at semanticOperation ⊢
      cases headSemantic :
          Fir.LeanIR.Impure.releaseResetField runtime value with
      | error fault =>
          rw [headSemantic] at semanticOperation
          contradiction
      | ok middleRuntime =>
          rw [headSemantic] at semanticOperation
          have releaseStep := head.releaseStep heap
            (state.heapCursor / headerBytes + 1) witness.closureDescriptors
          rcases releaseStep with heapChild | noOp
          · obtain ⟨location, valueEq, mapped⟩ := heapChild
            subst value
            have semanticHead : Fir.LeanIR.Impure.decLocation runtime location =
                .ok middleRuntime := by
              simpa [Fir.LeanIR.Impure.releaseResetField,
                Fir.LeanIR.Impure.decValueOnce] using headSemantic
            obtain ⟨middleState, concreteHead, middleHeap, capacityHead⟩ :=
              heap.decrementReferenceOnce_refines_with_capacity mapped true
                semanticHead
            obtain ⟨finalState, concreteTail, finalHeap, capacityTail⟩ :=
              ih middleHeap semanticOperation
            exact ⟨finalState, by rw [concreteHead]; exact concreteTail,
              finalHeap, capacityHead.trans capacityTail⟩
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
                          simpa [Fir.LeanIR.Impure.releaseResetField,
                            Fir.LeanIR.Impure.decValueOnce] using headSemantic
                        exact Except.ok.inj operation
                      exact equal.symm
              | usize value =>
                  simp [Fir.LeanIR.Impure.releaseResetField,
                    Fir.LeanIR.Impure.decValueOnce] at headSemantic
              | scalar value =>
                  simp [Fir.LeanIR.Impure.releaseResetField,
                    Fir.LeanIR.Impure.decValueOnce] at headSemantic
              | erased =>
                  have equal :
                      (Except.ok runtime : Except RuntimeFault RuntimeState) =
                        .ok middleRuntime := by
                    simpa [Fir.LeanIR.Impure.releaseResetField] using headSemantic
                  exact (Except.ok.inj equal).symm
              | reuseToken location =>
                  simp [Fir.LeanIR.Impure.releaseResetField,
                    Fir.LeanIR.Impure.decValueOnce] at headSemantic
            subst middleRuntime
            have concreteHead :
                decrementReferenceOnce state word true witness.closureDescriptors =
                .ok state := by
              unfold decrementReferenceOnce
              exact concreteFuelNoOp
            obtain ⟨finalState, concreteTail, finalHeap, capacityTail⟩ :=
              ih heap semanticOperation
            exact ⟨finalState, by rw [concreteHead]; exact concreteTail,
              finalHeap, capacityTail⟩

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
    resetObject state count word witness.closureDescriptors =
      .ok (state, Word32.zero) := by
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
      have releaseNoop :
          decrementReferenceOnce state word true witness.closureDescriptors =
            .ok state := by
        simpa using related.decrementReferenceOnce_tagged
          (TaggedReferenceRel.promoted found) true witness.closureDescriptors
      unfold resetObject
      rw [addressHeap, headerRead]
      simp only [Bind.bind, Except.bind, liftMemory]
      rw [if_pos (by simp [isPromoted])]
      rw [releaseNoop]
      rfl

/-- Reset rejects a canonical released allocation at the common live-header
gate, before ownership, constructor-kind, bounds, or child-release work. -/
theorem DeadCellRel.resetObject_eq
    {state : MemoryState} {address : Word32}
    (related : DeadCellRel state address) (count : Nat)
    (descriptors : ClosureDescriptorTable) :
    resetObject state count address descriptors =
      .error (.sourceAddress (.deadObject address)) := by
  obtain ⟨_, _, addressHeap, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    related.header
  unfold resetObject
  rw [addressHeap]
  simp only
  rw [related.readLiveHeader_eq]
  rfl

/-- Stale semantic and concrete reset operands agree on the exact
address-related dead-object fault. -/
theorem LiveHeapRel.resetObject_deadObject
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {address : Word32} {location : Location} {cell : HeapCell}
    (related : LiveHeapRel state witness runtime)
    (mapped : HeapReferenceRel witness address location)
    (found : findCell? runtime.heap location = some cell)
    (dead : cell.live = false) (count : Nat)
    (descriptors : ClosureDescriptorTable) :
    resetObject state count address descriptors =
        .error (.sourceAddress (.deadObject address)) ∧
      Fir.LeanIR.Impure.reset runtime count (.object (.heap location)) =
        .error (.deadObject location) := by
  have deadRelated := related.deadCellRel mapped found dead
  exact ⟨deadRelated.resetObject_eq count descriptors, by
    simp [Fir.LeanIR.Impure.reset, getLiveCell, found, dead]
    rfl⟩

/-- A live, ordinary, uniquely owned nonconstructor reaches reset's
constructor-kind gate in both runtimes. These premises state the exact
precedence boundary: shared/persistent objects take the decrement fallback,
while dead objects fail at the earlier live-header read. -/
theorem LiveHeapRel.resetObject_expectedConstructor_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {address : Word32} {location : Location} {cell : HeapCell}
    (related : LiveHeapRel state witness runtime)
    (mapped : HeapReferenceRel witness address location)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true) (ordinary : cell.persistent = false)
    (unique : cell.rc = 1)
    (notConstructor : ∀ object, cell.object ≠ .ctor object)
    (count : Nat) (descriptors : ClosureDescriptorTable) :
    resetObject state count address descriptors =
        .error (.source .expectedConstructor) ∧
      Fir.LeanIR.Impure.reset runtime count (.object (.heap location)) =
        .error .expectedConstructor := by
  have failOfHeader (header : Header)
      (headerRead : state.readLiveHeader address = .ok header)
      (headerKind : header.kind ≠ .constructor)
      (notPromoted : header.isPromotedTag = false)
      (refCount : header.refCount.toNat = cell.rc)
      (persistent : header.persistent = cell.persistent) :
      resetObject state count address descriptors =
        .error (.source .expectedConstructor) := by
    have addressHeap :=
      (MemoryState.PrefixExtension.readLiveHeader_facts state address header
        headerRead).1
    have headerOne : header.refCount = 1 := by
      apply UInt32.toNat.inj
      simpa [unique] using refCount
    have headerOrdinary : header.persistent = false :=
      persistent.trans ordinary
    unfold resetObject
    rw [addressHeap, headerRead]
    simp only [Bind.bind, Except.bind, liftMemory]
    rw [if_neg (by simp [notPromoted, headerOrdinary, headerOne])]
    cases kindEq : header.kind <;> simp_all <;> rfl
  have mappedLookup :
      witness.locations.lookup? location = some address := by
    cases mapped with
    | mapped found => exact found
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mappedLookup
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  have concrete :
      resetObject state count address descriptors =
        .error (.source .expectedConstructor) := by
    cases targetRelated with
    | constructor descriptor objectEq objectRelated headerRead headerKind
        refCount persistent cellLive =>
        exact False.elim (notConstructor _ objectEq)
    | boxed descriptor objectEq objectRelated refCount persistent cellLive =>
        have different :
            (ObjectKind.boxed == ObjectKind.natural) = false := by
          decide
        exact failOfHeader _ objectRelated.headerRead
          (by simp [objectRelated.headerKind])
          (by simp [Header.isPromotedTag, objectRelated.headerKind, different])
          refCount persistent
    | natural descriptor objectEq headerRead headerKind marker extent limbsFit
        decoded refCount persistent cellLive =>
        exact failOfHeader _ headerRead (by simp [headerKind])
          (by simp [Header.isPromotedTag, headerKind, marker,
            bigNaturalMarker, promotedTagMarker])
          refCount persistent
    | integer descriptor objectEq objectRelated refCount persistent cellLive =>
        have different :
            (ObjectKind.integer == ObjectKind.natural) = false := by
          decide
        exact failOfHeader _ objectRelated.headerRead
          (by simp [objectRelated.headerKind])
          (by simp [Header.isPromotedTag, objectRelated.headerKind, different])
          refCount persistent
    | string descriptor objectEq objectRelated refCount persistent cellLive =>
        have different :
            (ObjectKind.string == ObjectKind.natural) = false := by
          decide
        exact failOfHeader _ objectRelated.headerRead
          (by simp [objectRelated.headerKind])
          (by simp [Header.isPromotedTag, objectRelated.headerKind, different])
          refCount persistent
    | closure closureRelated =>
        cases closureRelated with
        | closure objectEq objectRelated headerRead headerKind descriptorLookup
            fixedCount extent refCount persistent cellLive =>
            have different :
                (ObjectKind.closure == ObjectKind.natural) = false := by
              decide
            exact failOfHeader _ headerRead (by simp [headerKind])
              (by simp [Header.isPromotedTag, headerKind, different])
              refCount persistent
  have semantic :
      Fir.LeanIR.Impure.reset runtime count (.object (.heap location)) =
        .error .expectedConstructor := by
    unfold Fir.LeanIR.Impure.reset
    simp only [getLiveCell, found, live, ↓reduceIte, Bind.bind, Except.bind]
    rw [if_neg (by simp [ordinary, unique])]
    cases objectEq : cell.object with
    | ctor object => exact False.elim (notConstructor object objectEq)
    | closure function arity fixed => rfl
    | boxed type value => rfl
    | string value => rfl
    | natural value => rfl
    | integer value => rfl
    | byteArray value => rfl
    | «opaque» typeName => rfl
  exact ⟨concrete, semantic⟩

/-- A live, ordinary, uniquely owned constructor with an oversized reset
prefix reaches the bounds gate in both runtimes. No field is cleared and no
child ownership is released on this branch. -/
theorem LiveHeapRel.resetObject_outOfBounds_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {address : Word32} {location : Location} {cell : HeapCell}
    {object : ConstructorObject}
    (related : LiveHeapRel state witness runtime)
    (mapped : HeapReferenceRel witness address location)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true) (ordinary : cell.persistent = false)
    (unique : cell.rc = 1) (constructor : cell.object = .ctor object)
    (count : Nat) (outOfBounds : object.objectFields.size < count)
    (descriptors : ClosureDescriptorTable) :
    resetObject state count address descriptors =
        .error
          (.source (.objectFieldOutOfBounds count object.objectFields.size)) ∧
      Fir.LeanIR.Impure.reset runtime count (.object (.heap location)) =
        .error (.objectFieldOutOfBounds count object.objectFields.size) := by
  have mappedLookup :
      witness.locations.lookup? location = some address := by
    cases mapped with
    | mapped found => exact found
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mappedLookup
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  have concrete :
      resetObject state count address descriptors =
        .error
          (.source (.objectFieldOutOfBounds count object.objectFields.size)) := by
    cases targetRelated with
    | @constructor info fieldKinds semantic header _ descriptor objectEq
        objectRelated headerRead headerKind refCount persistent cellLive =>
        rw [constructor] at objectEq
        injection objectEq with semanticEq
        subst semantic
        have addressHeap :=
          (MemoryState.PrefixExtension.readLiveHeader_facts state address header
            headerRead).1
        have headerOrdinary : header.persistent = false :=
          persistent.trans ordinary
        have headerOne : header.refCount = 1 := by
          apply UInt32.toNat.inj
          simpa [unique] using refCount
        have notPromoted : header.isPromotedTag = false := by
          have different :
              (ObjectKind.constructor == ObjectKind.natural) = false := by
            decide
          simp [Header.isPromotedTag, headerKind, different]
        obtain ⟨objectHeader, objectHeaderRead, _, _, _, objectCount, _, _⟩ :=
          objectRelated.header
        rw [headerRead] at objectHeaderRead
        have objectHeaderEq := Except.ok.inj objectHeaderRead
        subst objectHeader
        have outOfBoundsInfo : info.size < count := by
          rw [← objectRelated.semanticObjectFields]
          exact outOfBounds
        have headerKindCheck :
            (header.kind == ObjectKind.constructor) = true := by
          rw [headerKind]
          decide
        unfold resetObject
        rw [addressHeap, headerRead]
        simp only [Bind.bind, Except.bind, liftMemory]
        rw [if_neg (by simp [notPromoted, headerOrdinary, headerOne])]
        rw [if_pos headerKindCheck]
        rw [objectCount, if_pos outOfBoundsInfo]
        rw [objectRelated.semanticObjectFields]
        rfl
    | boxed descriptor objectEq objectRelated refCount persistent cellLive =>
        rw [constructor] at objectEq
        contradiction
    | natural descriptor objectEq headerRead headerKind marker extent limbsFit
        decoded refCount persistent cellLive =>
        rw [constructor] at objectEq
        contradiction
    | integer descriptor objectEq objectRelated refCount persistent cellLive =>
        rw [constructor] at objectEq
        contradiction
    | string descriptor objectEq objectRelated refCount persistent cellLive =>
        rw [constructor] at objectEq
        contradiction
    | closure closureRelated =>
        obtain ⟨function, arity, captures, closureEq⟩ :=
          closureRelated.objectEq
        rw [constructor] at closureEq
        contradiction
  have semantic :
      Fir.LeanIR.Impure.reset runtime count (.object (.heap location)) =
        .error (.objectFieldOutOfBounds count object.objectFields.size) := by
    unfold Fir.LeanIR.Impure.reset
    simp only [getLiveCell, found, live, ↓reduceIte, Bind.bind, Except.bind]
    rw [if_neg (by simp [ordinary, unique])]
    rw [constructor]
    simp only
    rw [if_pos outOfBounds]
    rfl
  exact ⟨concrete, semantic⟩

/-- The tagged reset equation agrees with FIR and returns the related empty
reuse token. -/
theorem LiveHeapRel.resetObject_refines_tagged
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {payload : UInt64} {word : Word32}
    (related : LiveHeapRel state witness runtime)
    (tagged : TaggedReferenceRel witness word payload) (count : Nat) :
    resetObject state count word witness.closureDescriptors =
      .ok (state, Word32.zero) ∧
      Fir.LeanIR.Impure.reset runtime count (.object (.tagged payload)) =
        .ok (runtime, .reuseToken none) ∧
      ValueRel witness .reuseToken (.word32 Word32.zero) (.reuseToken none) := by
  exact ⟨related.resetObject_tagged tagged count, rfl, .reuseNone⟩

/-- A non-unique ordinary heap cell follows reset's fallback path: one public
decrement is performed, the empty reuse token is returned, and every mapped
header retains its physical extent. -/
theorem LiveHeapRel.resetObject_refines_nonunique_with_capacity
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
      resetObject state count address witness.closureDescriptors =
        .ok (result, Word32.zero) ∧
      LiveHeapRel result witness nextRuntime ∧
      ValueRel witness .reuseToken (.word32 Word32.zero) (.reuseToken none) ∧
      MappedHeaderCapacityTransport state result witness := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  obtain ⟨header, headerRead, _, notPromoted, _, refCount⟩ :=
    targetRelated.ownershipHeader
  have headerCountNe : header.refCount ≠ 1 := by
    intro one
    rw [one] at refCount
    simp at refCount
    exact notUnique refCount.symm
  have fallback :
      (header.isPromotedTag || header.persistent || header.refCount != 1) = true := by
    simp [notPromoted, headerCountNe]
  have semanticDec :
      Fir.LeanIR.Impure.decLocation runtime location = .ok nextRuntime := by
    unfold Fir.LeanIR.Impure.reset at semanticOperation
    simp only [getLiveCell, found, live, ↓reduceIte, Bind.bind, Except.bind]
      at semanticOperation
    rw [if_pos (by simp [notUnique])]
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
  obtain ⟨result, concreteDec, finalRelated, capacityTransport⟩ :=
    related.decrementReferenceOnce_refines_with_capacity mapped true semanticDec
  have addressHeap :=
    (MemoryState.PrefixExtension.readLiveHeader_facts state address header
      headerRead).1
  have concreteReset :
      resetObject state count address witness.closureDescriptors =
        .ok (result, Word32.zero) := by
    unfold resetObject
    rw [addressHeap, headerRead]
    simp only [Bind.bind, Except.bind, liftMemory]
    rw [if_pos fallback, concreteDec]
    rfl
  exact ⟨result, concreteReset, finalRelated, .reuseNone, capacityTransport⟩

/-- Compatibility surface for clients that need only heap and value
refinement from the nonunique reset branch. -/
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
      resetObject state count address witness.closureDescriptors =
        .ok (result, Word32.zero) ∧
      LiveHeapRel result witness nextRuntime ∧
      ValueRel witness .reuseToken (.word32 Word32.zero)
        (.reuseToken none) := by
  obtain ⟨result, concreteReset, finalRelated, tokenRelated, _⟩ :=
    related.resetObject_refines_nonunique_with_capacity mapped found live
      notUnique semanticOperation
  exact ⟨result, concreteReset, finalRelated, tokenRelated⟩

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
      resetObject state count address witness.closureDescriptors =
        .ok (result, address) ∧
      LiveHeapRel result
        (witness.rebindConstructor address info
          (resetProtocolFieldKinds fieldKinds count)) nextRuntime ∧
      ResetReuseProtocolRel state result witness runtime nextRuntime location
        address cell object count ∧
      ValueRel
        (witness.rebindConstructor address info
          (resetProtocolFieldKinds fieldKinds count))
        .reuseToken (.word32 address) (.reuseToken (some location)) ∧
      MappedHeaderCapacityTransport state result witness := by
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
              (fun next value => Fir.LeanIR.Impure.releaseResetField next value)
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
              (fun next value => Fir.LeanIR.Impure.releaseResetField next value)
              next
            return (next, Value.reuseToken (some location))) =
              .ok (nextRuntime, Value.reuseToken (some location)) := by
          simpa only [replacement, resetProtocolObject, live, Bind.bind, Except.bind]
            using semanticOperation
        rw [semanticSet] at semanticOperation'
        simp only [Bind.bind, Except.bind] at semanticOperation'
        cases foldEq : (object.objectFields.extract 0 count).foldlM
            (fun next value => Fir.LeanIR.Impure.releaseResetField next value)
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
      obtain ⟨protocolRuntime, protocolSet, protocolHeap, prefixCapacity⟩ :=
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
              (fun next value => Fir.LeanIR.Impure.releaseResetField next value) =
            .ok nextRuntime := by
        simpa only [Array.foldlM_toList] using semanticFold
      have protocolOwnership := ownershipRelated.rebindConstructor address info
        (resetProtocolFieldKinds fieldKinds count)
      obtain ⟨result, concreteFold, finalHeap, foldCapacity⟩ :=
        protocolOwnership.foldlM_public_refines protocolHeap semanticFoldList
      have foldCapacityOriginal :
          MappedHeaderCapacityTransport
            ({ state with memory := fieldMemory } : MemoryState) result
              witness := by
        intro mappedAddress mappedLocation mappedHeader mappedBefore
          mappedRead mappedOwned
        exact foldCapacity mappedAddress mappedLocation mappedHeader
          (by
            simpa [RefinementWitness.rebindConstructor] using mappedBefore)
          mappedRead mappedOwned
      have capacity : MappedHeaderCapacityTransport state result witness :=
        prefixCapacity.trans foldCapacityOriginal
      obtain ⟨addressHeap, _, _, _, _, _⟩ :=
        MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead
      obtain ⟨objectHeader, objectHeaderRead, _, _, _, objectCount, _, _⟩ :=
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
      have concreteFoldOriginal :
          words.foldlM (init := ({ state with memory := fieldMemory } : MemoryState))
            (fun next child => decrementReferenceOnce next child true
              witness.closureDescriptors) = .ok result := by
        simpa [RefinementWitness.rebindConstructor] using concreteFold
      have concreteReset :
          resetObject state count address witness.closureDescriptors =
            .ok (result, address) := by
        unfold resetObject
        rw [addressHeap, headerRead]
        simp only [Bind.bind, Except.bind, liftMemory]
        rw [if_neg (by simp [notPromoted, headerOrdinary, headerOne])]
        rw [if_pos headerKindCheck]
        rw [objectCount, if_neg (Nat.not_lt.mpr countFitsInfo)]
        rw [ownedRead, fieldWrite]
        simp only
        rw [concreteFoldOriginal]
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
          (resetProtocolFieldKinds fieldKinds count), capacity⟩
  | boxed descriptor objectEq objectRelated refCount persistent cellLive =>
      rw [constructor] at objectEq
      contradiction
  | natural descriptor objectEq headerRead headerKind marker extent
      limbsFit decoded refCount persistent cellLive =>
      rw [constructor] at objectEq
      contradiction
  | integer descriptor objectEq objectRelated refCount persistent cellLive =>
      rw [constructor] at objectEq
      contradiction
  | string descriptor objectEq objectRelated refCount persistent cellLive =>
      rw [constructor] at objectEq
      contradiction
  | closure closureRelated =>
      obtain ⟨function, arity, captures, closureEq⟩ := closureRelated.objectEq
      rw [constructor] at closureEq
      contradiction

/-- Reuse rejects a canonical released token at the common live-header gate
after the statically aligned field-arity check. -/
theorem DeadCellRel.reuseObject_eq
    {state : MemoryState} {address : Word32}
    (related : DeadCellRel state address) (info : LCNF.CtorInfo)
    (updateHeader : Bool) (fields : Array Word32)
    (arity : fields.size = info.size) :
    reuseObject state address info updateHeader fields =
      .error (.sourceAddress (.deadObject address)) := by
  obtain ⟨_, _, addressHeap, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    related.header
  have addressNeZero : address ≠ Word32.zero := by
    intro equal
    subst address
    change ObjectWordClass.sentinel = ObjectWordClass.heap at addressHeap
    contradiction
  have addressValueNeZero : address.value ≠ 0 := by
    intro equal
    have sentinel : address.classify = .sentinel := by
      simp [Word32.classify, equal]
    rw [sentinel] at addressHeap
    contradiction
  have addressZeroCheck : (address == Word32.zero) = false := by
    change (address.value == 0) = false
    simp [addressValueNeZero]
  unfold reuseObject
  rw [if_neg (by simp [addressZeroCheck])]
  rw [addressHeap]
  simp only
  rw [if_pos arity]
  rw [related.readLiveHeader_eq]
  rfl

/-- Stale semantic and concrete nonempty reuse tokens agree on the exact
address-related dead-object fault. The arity premises expose the earlier
static gate in both runtimes. -/
theorem LiveHeapRel.reuseObject_deadObject
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {address : Word32} {location : Location} {cell : HeapCell}
    (related : LiveHeapRel state witness runtime)
    (mapped : HeapReferenceRel witness address location)
    (found : findCell? runtime.heap location = some cell)
    (dead : cell.live = false) (info : LCNF.CtorInfo)
    (updateHeader : Bool) (fields : Array Word32)
    (semanticFields : Array Value)
    (arity : fields.size = info.size)
    (semanticArity : semanticFields.size = info.size) :
    reuseObject state address info updateHeader fields =
        .error (.sourceAddress (.deadObject address)) ∧
      Fir.LeanIR.Impure.reuse runtime (.reuseToken (some location)) info
          updateHeader semanticFields =
        .error (.deadObject location) := by
  have deadRelated := related.deadCellRel mapped found dead
  have semantic :
      Fir.LeanIR.Impure.reuse runtime (.reuseToken (some location)) info
          updateHeader semanticFields =
        .error (.deadObject location) := by
    unfold Fir.LeanIR.Impure.reuse
    simp only
    have arityCheck : (semanticFields.size != info.size) = false := by
      simp [semanticArity]
    rw [arityCheck]
    simp [getLiveCell, found, dead]
    rfl
  exact ⟨deadRelated.reuseObject_eq info updateHeader fields arity, semantic⟩

/-- A live nonconstructor behind a nonempty reuse token reaches the
constructor-kind gate in both runtimes. Token shape and field arity are
separate earlier gates and therefore explicit premises. -/
theorem LiveHeapRel.reuseObject_expectedConstructor_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {address : Word32} {location : Location} {cell : HeapCell}
    (related : LiveHeapRel state witness runtime)
    (mapped : HeapReferenceRel witness address location)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (notConstructor : ∀ object, cell.object ≠ .ctor object)
    (info : LCNF.CtorInfo) (updateHeader : Bool)
    (fields : Array Word32) (semanticFields : Array Value)
    (arity : fields.size = info.size)
    (semanticArity : semanticFields.size = info.size) :
    reuseObject state address info updateHeader fields =
        .error (.source .expectedConstructor) ∧
      Fir.LeanIR.Impure.reuse runtime (.reuseToken (some location)) info
          updateHeader semanticFields =
        .error .expectedConstructor := by
  have failOfHeader (header : Header)
      (headerRead : state.readLiveHeader address = .ok header)
      (headerKind : header.kind ≠ .constructor) :
      reuseObject state address info updateHeader fields =
        .error (.source .expectedConstructor) := by
    have addressHeap :=
      (MemoryState.PrefixExtension.readLiveHeader_facts state address header
        headerRead).1
    have addressNeZero : address ≠ Word32.zero := by
      intro equal
      subst address
      change ObjectWordClass.sentinel = ObjectWordClass.heap at addressHeap
      contradiction
    have addressValueNeZero : address.value ≠ 0 := by
      intro equal
      have sentinel : address.classify = .sentinel := by
        simp [Word32.classify, equal]
      rw [sentinel] at addressHeap
      contradiction
    have addressZeroCheck : (address == Word32.zero) = false := by
      change (address.value == 0) = false
      simp [addressValueNeZero]
    unfold reuseObject
    rw [if_neg (by simp [addressZeroCheck])]
    rw [addressHeap]
    simp only
    rw [if_pos arity]
    rw [headerRead]
    simp only [Bind.bind, Except.bind, liftMemory]
    cases kindEq : header.kind <;> simp_all <;> rfl
  have mappedLookup :
      witness.locations.lookup? location = some address := by
    cases mapped with
    | mapped found => exact found
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mappedLookup
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  have concrete :
      reuseObject state address info updateHeader fields =
        .error (.source .expectedConstructor) := by
    cases targetRelated with
    | constructor descriptor objectEq objectRelated headerRead headerKind
        refCount persistent cellLive =>
        exact False.elim (notConstructor _ objectEq)
    | boxed descriptor objectEq objectRelated refCount persistent cellLive =>
        exact failOfHeader _ objectRelated.headerRead
          (by simp [objectRelated.headerKind])
    | natural descriptor objectEq headerRead headerKind marker extent limbsFit
        decoded refCount persistent cellLive =>
        exact failOfHeader _ headerRead (by simp [headerKind])
    | integer descriptor objectEq objectRelated refCount persistent cellLive =>
        exact failOfHeader _ objectRelated.headerRead
          (by simp [objectRelated.headerKind])
    | string descriptor objectEq objectRelated refCount persistent cellLive =>
        exact failOfHeader _ objectRelated.headerRead
          (by simp [objectRelated.headerKind])
    | closure closureRelated =>
        cases closureRelated with
        | closure objectEq objectRelated headerRead headerKind descriptorLookup
            fixedCount extent refCount persistent cellLive =>
            exact failOfHeader _ headerRead (by simp [headerKind])
  have semantic :
      Fir.LeanIR.Impure.reuse runtime (.reuseToken (some location)) info
          updateHeader semanticFields =
        .error .expectedConstructor := by
    unfold Fir.LeanIR.Impure.reuse
    simp only
    have arityCheck : (semanticFields.size != info.size) = false := by
      simp [semanticArity]
    rw [arityCheck]
    simp only [Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind]
    have liveCell : getLiveCell runtime location = .ok cell := by
      simp [getLiveCell, found, live]
    rw [liveCell]
    simp only
    cases objectEq : cell.object with
    | ctor object => exact False.elim (notConstructor object objectEq)
    | closure function arity fixed => rfl
    | boxed type value => rfl
    | string value => rfl
    | natural value => rfl
    | integer value => rfl
    | byteArray value => rfl
    | «opaque» typeName => rfl
  exact ⟨concrete, semantic⟩

/-- Consuming an empty reuse token for an empty-layout constructor preserves
the semantic tagged-constructor representation. The concrete word may be a
direct immediate or a fresh promoted tag; `encodeTagged_liveHeapRel` supplies
the exact witness in either case. -/
theorem LiveHeapRel.reuseObject_none_refines_empty
    (state result : MemoryState) (witness : RefinementWitness)
    (runtime : RuntimeState) (info : LCNF.CtorInfo)
    (fields : Array Word32) (semanticFields : Array Value)
    (word : Word32) (updateHeader : Bool)
    (related : LiveHeapRel state witness runtime)
    (arity : fields.size = info.size)
    (semanticArity : semanticFields.size = info.size)
    (empty : (info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0)
    (tagFits : info.cidx < UInt32.size)
    (reused : reuseObject state Word32.zero info updateHeader fields =
      .ok (result, word)) :
    ∃ nextWitness,
      LiveHeapRel result nextWitness runtime ∧
      ValueRel nextWitness .tobject (.word32 word)
        (.object (.tagged (UInt64.ofNat info.cidx))) ∧
      Fir.LeanIR.Impure.reuse runtime (.reuseToken none) info updateHeader
          semanticFields =
        .ok (runtime, .object (.tagged (UInt64.ofNat info.cidx))) := by
  have allocated : allocateConstructor state info fields = .ok (result, word) := by
    unfold reuseObject at reused
    rw [if_pos (by decide)] at reused
    exact reused
  have encoded : encodeTagged state (UInt64.ofNat info.cidx) =
      .ok (result, word) := by
    unfold allocateConstructor at allocated
    rw [if_pos arity] at allocated
    rw [uint32Field_eq_ok "constructor tag" info.cidx tagFits] at allocated
    simp only [Bind.bind, Except.bind] at allocated
    rw [if_pos (by simp [empty.1.1, empty.1.2, empty.2])] at allocated
    simpa [UInt32.toNat_ofNat_of_lt' tagFits] using allocated
  obtain ⟨nextWitness, heapRelated, valueRelated⟩ :=
    encodeTagged_liveHeapRel state result witness runtime
      (UInt64.ofNat info.cidx) word related encoded
  have semanticAllocation :
      allocCtor runtime info semanticFields =
        .ok (runtime, .object (.tagged (UInt64.ofNat info.cidx))) := by
    simp [allocCtor, semanticArity, empty.1.1, empty.1.2, empty.2]
    rfl
  exact ⟨nextWitness, heapRelated, valueRelated, by
    simpa [Fir.LeanIR.Impure.reuse] using semanticAllocation⟩

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

/-- Consuming a nonempty reuse token performs the checked in-place concrete
transaction and FIR's semantic cell replacement in lockstep. The compiler
supplies the retained-capacity and metadata-width obligations; the same
semantic location is returned under the ordinary replacement descriptor. -/
theorem LiveHeapRel.reuseObject_some_refines
    (state : MemoryState) (witness : RefinementWitness)
    (runtime : RuntimeState) (location : Location) (address : Word32)
    (cell : HeapCell) (oldInfo : LCNF.CtorInfo)
    (oldFieldKinds : Array AbiKind) (old : ConstructorObject)
    (info : LCNF.CtorInfo) (fieldKinds : Array AbiKind)
    (fields : Array Word32) (semanticFields : Array Value)
    (updateHeader : Bool) (header : Header)
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (descriptor : witness.descriptors.lookup? address =
      some (.constructor oldInfo oldFieldKinds))
    (objectEq : cell.object = .ctor old)
    (objectRelated : ConstructorObjectRel state witness address oldInfo
      oldFieldKinds old)
    (headerRead : state.readLiveHeader address = .ok header)
    (headerKind : header.kind = .constructor)
    (refCount : header.refCount.toNat = cell.rc)
    (persistent : header.persistent = cell.persistent)
    (ordinary : cell.persistent = false)
    (cellLive : cell.live = true)
    (layoutFits : (ConstructorLayout.ofInfo info).allocationBytes ≤
      header.allocationBytes.toNat)
    (arity : fields.size = info.size)
    (semanticArity : semanticFields.size = info.size)
    (fieldKindsSize : fieldKinds.size = info.size)
    (fieldKindsValid : fieldKinds.all AbiKind.isObjectField = true)
    (fieldRelated : ∀ (index : Nat) (kind : AbiKind) (value : Value),
      fieldKinds[index]? = some kind →
      semanticFields[index]? = some value →
      ∃ word, fields[index]? = some word ∧
        ValueRel witness kind (.word32 word) value)
    (tagFits : info.cidx < UInt32.size)
    (objectFieldsFit : info.size < UInt32.size)
    (usizeFieldsFit : info.usize < UInt32.size)
    (scalarBytesFit : info.ssize < UInt32.size) :
    ∃ result nextRuntime,
      reuseObject state address info updateHeader fields = .ok (result, address) ∧
      Fir.LeanIR.Impure.reuse runtime (.reuseToken (some location)) info
          updateHeader semanticFields =
        .ok (nextRuntime, .object (.heap location)) ∧
      LiveHeapRel result (witness.rebindConstructor address info fieldKinds)
        nextRuntime ∧
      ValueRel (witness.rebindConstructor address info fieldKinds) .object
        (.word32 address) (.object (.heap location)) ∧
      MappedHeaderCapacityTransport state result witness := by
  obtain ⟨addressHeap, _, _, headerMinimum, _, headerInBounds⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead
  let objectHeader := objectRelated.header.choose
  obtain ⟨objectHeaderRead, _, _, oldTag, _, _, _⟩ :=
    objectRelated.header.choose_spec
  change state.readLiveHeader address = .ok objectHeader at objectHeaderRead
  change objectHeader.aux0.toNat = old.tag at oldTag
  rw [headerRead] at objectHeaderRead
  have objectHeaderEq := Except.ok.inj objectHeaderRead
  rw [← objectHeaderEq] at oldTag
  let tag : UInt32 :=
    if updateHeader then UInt32.ofNat info.cidx else header.aux0
  let replacement : Header := {
    header with
    kind := .constructor
    persistent := false
    live := true
    aux0 := tag
    aux1 := UInt32.ofNat info.size
    aux2 := UInt32.ofNat info.usize
    aux3 := UInt32.ofNat info.ssize }
  have tagToNat : tag.toNat = if updateHeader then info.cidx else old.tag := by
    cases updateHeader <;>
      simp [tag, oldTag, UInt32.toNat_ofNat_of_lt' tagFits]
  have objectFieldsToNat : (UInt32.ofNat info.size).toNat = info.size :=
    UInt32.toNat_ofNat_of_lt' objectFieldsFit
  have usizeFieldsToNat : (UInt32.ofNat info.usize).toNat = info.usize :=
    UInt32.toNat_ofNat_of_lt' usizeFieldsFit
  have scalarBytesToNat : (UInt32.ofNat info.ssize).toNat = info.ssize :=
    UInt32.toNat_ofNat_of_lt' scalarBytesFit
  have fieldsInAllocation : objectFieldAddress address.value fields.toList.length ≤
      address.value + header.allocationBytes.toNat := by
    have aligned := align8_ge
      (headerBytes + target.semanticSlotBytes * (info.size + info.usize) + info.ssize)
    simp [ConstructorLayout.ofInfo, target] at aligned layoutFits
    simp [objectFieldAddress, arity, target]
    omega
  obtain ⟨scrubbed, fieldMemory, memory, transaction, post⟩ :=
    state.memory.reuseConstructorMemory_spec address header.allocationBytes.toNat
      replacement fields.toList headerMinimum headerInBounds fieldsInAllocation
  have replacementKind : replacement.kind = .constructor := by rfl
  have replacementLive : replacement.live = true := by rfl
  have replacementPersistent : replacement.persistent = false := by rfl
  have replacementRefCount : replacement.refCount = header.refCount := by rfl
  have replacementAllocation :
      replacement.allocationBytes = header.allocationBytes := by rfl
  have replacementTag : replacement.aux0.toNat =
      if updateHeader then info.cidx else old.tag := by
    exact tagToNat
  have replacementObjectFields : replacement.aux1.toNat = info.size := by
    exact objectFieldsToNat
  have replacementUSizeFields : replacement.aux2.toNat = info.usize := by
    exact usizeFieldsToNat
  have replacementScalarBytes : replacement.aux3.toNat = info.ssize := by
    exact scalarBytesToNat
  obtain ⟨nextRuntime, semanticSet, finalHeap⟩ :=
    related.setCell_ofReuseConstructorMemory state memory scrubbed fieldMemory
      witness runtime location address cell oldInfo oldFieldKinds old info fieldKinds
      fields semanticFields updateHeader header replacement mapped found descriptor
      objectEq objectRelated headerRead headerKind refCount persistent ordinary cellLive
      replacementKind replacementLive replacementPersistent replacementRefCount
      replacementAllocation replacementTag replacementObjectFields
      replacementUSizeFields replacementScalarBytes layoutFits arity semanticArity
      fieldKindsSize fieldKindsValid fieldRelated transaction post
  have addressNeZero : address ≠ Word32.zero := by
    intro equal
    subst address
    change ObjectWordClass.sentinel = ObjectWordClass.heap at addressHeap
    contradiction
  have addressValueNeZero : address.value ≠ 0 := by
    intro equal
    have sentinel : address.classify = .sentinel := by
      simp [Word32.classify, equal]
    rw [sentinel] at addressHeap
    contradiction
  have addressZeroCheck : (address == Word32.zero) = false := by
    change (address.value == 0) = false
    simp [addressValueNeZero]
  have headerKindCheck : (header.kind == ObjectKind.constructor) = true := by
    rw [headerKind]
    decide
  have concreteReuse :
      reuseObject state address info updateHeader fields =
        .ok (({ state with memory } : MemoryState), address) := by
    unfold reuseObject
    rw [if_neg (by simp [addressZeroCheck])]
    rw [addressHeap]
    simp only
    rw [if_pos arity]
    rw [headerRead]
    simp only [Bind.bind, Except.bind, liftMemory]
    rw [if_pos headerKindCheck]
    rw [if_pos layoutFits]
    cases updateHeader with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [show (pure header.aux0 : Except ConcreteError UInt32) =
        .ok header.aux0 by rfl]
      simp only
      rw [uint32Field_eq_ok "object-field count" info.size objectFieldsFit]
      simp only
      rw [uint32Field_eq_ok "usize-field count" info.usize usizeFieldsFit]
      simp only
      rw [uint32Field_eq_ok "scalar byte count" info.ssize scalarBytesFit]
      simp only
      have transaction' := transaction
      simp [tag, replacement] at transaction'
      rw [transaction']
      rfl
    | true =>
      simp only [↓reduceIte]
      rw [uint32Field_eq_ok "constructor tag" info.cidx tagFits]
      simp only
      rw [uint32Field_eq_ok "object-field count" info.size objectFieldsFit]
      simp only
      rw [uint32Field_eq_ok "usize-field count" info.usize usizeFieldsFit]
      simp only
      rw [uint32Field_eq_ok "scalar byte count" info.ssize scalarBytesFit]
      simp only
      have transaction' := transaction
      simp [tag, replacement] at transaction'
      rw [transaction']
      rfl
  have semanticReuse :
      Fir.LeanIR.Impure.reuse runtime (.reuseToken (some location)) info
          updateHeader semanticFields =
        .ok (nextRuntime, .object (.heap location)) := by
    have liveCell : getLiveCell runtime location = .ok cell := by
      simp [getLiveCell, found, cellLive]
    have arityCheck : (semanticFields.size != info.size) = false := by
      simp [semanticArity]
    unfold Fir.LeanIR.Impure.reuse
    simp only
    rw [arityCheck]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [liveCell]
    simp only [Bind.bind, Except.bind]
    rw [objectEq]
    simp only
    have reusedEq :
        ({ tag := if updateHeader then info.cidx else old.tag
           objectFields := semanticFields
           usizeFields := Array.replicate info.usize 0
           scalarFields := [] } : ConstructorObject) =
          reusedConstructorObject old info updateHeader semanticFields := by
      rfl
    rw [reusedEq]
    rw [semanticSet]
    rfl
  have capacityTransport :
      MappedHeaderCapacityTransport state
        ({ state with memory } : MemoryState) witness :=
    related.mappedHeaderCapacity_of_reuseConstructorMemory descriptor
      (by
        obtain ⟨_, rawHeaderRead, _, _, _, _⟩ :=
          MemoryState.PrefixExtension.readLiveHeader_facts state address header
            headerRead
        exact rawHeaderRead)
      rfl post replacementAllocation
  exact ⟨({ state with memory } : MemoryState), nextRuntime, concreteReuse,
    semanticReuse, finalHeap, .object (.mapped (by simpa using mapped)),
    capacityTransport⟩

end Fir.Wasm.Concrete
