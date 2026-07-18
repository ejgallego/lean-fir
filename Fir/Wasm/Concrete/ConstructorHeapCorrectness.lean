import Fir.Wasm.Concrete.ConstructorAllocationCorrectness

namespace Fir.Wasm.Concrete

open Lean.Compiler
open Fir.LeanIR.Impure

def semanticConstructorObject (info : LCNF.CtorInfo) (fields : Array Value) :
    ConstructorObject := {
  tag := info.cidx
  objectFields := fields
  usizeFields := Array.replicate info.usize 0
  scalarFields := [] }

def semanticConstructorCell (info : LCNF.CtorInfo) (fields : Array Value) :
    HeapCell := { object := .ctor (semanticConstructorObject info fields) }

def semanticConstructorResult (runtime : RuntimeState) (info : LCNF.CtorInfo)
    (fields : Array Value) : RuntimeState := {
  runtime with
  heap := (runtime.nextLocation, semanticConstructorCell info fields) :: runtime.heap
  nextLocation := runtime.nextLocation + 1 }

@[simp] theorem allocCtor_nonempty_eq (runtime : RuntimeState)
    (info : LCNF.CtorInfo) (fields : Array Value)
    (arity : fields.size = info.size)
    (nonempty : ¬ ((info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0)) :
    allocCtor runtime info fields = .ok
      (semanticConstructorResult runtime info fields,
        .object (.heap runtime.nextLocation)) := by
  unfold allocCtor
  simp [arity, nonempty, semanticConstructorResult, semanticConstructorCell,
    semanticConstructorObject, alloc]
  rfl

/-- A nonempty constructor allocation extends the complete concrete/semantic
live-heap relation and relates the returned concrete address to the fresh
semantic location.  This is the W6.1 operation-level refinement boundary
needed by the W2 constructor host contract. -/
theorem allocateConstructor_nonempty_liveHeapRel
    (state result : MemoryState) (witness : RefinementWitness)
    (runtime : RuntimeState) (info : LCNF.CtorInfo)
    (fieldKinds : Array AbiKind) (fields : Array Word32)
    (semanticFields : Array Value) (address : Word32)
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
    (allocated : allocateConstructor state info fields = .ok (result, address)) :
    let nextWitness := witness.bindConstructor runtime.nextLocation address info fieldKinds
    LiveHeapRel result nextWitness
        (semanticConstructorResult runtime info semanticFields) ∧
      ValueRel nextWitness .object (.word32 address)
        (.object (.heap runtime.nextLocation)) := by
  dsimp only
  obtain ⟨middle, objectAllocation, _, _⟩ :=
    allocateConstructor_nonempty_decompose state result info fields address arity
      nonempty tagFits objectFieldsFit usizeFieldsFit scalarBytesFit allocated
  have freshAddress := related.frontier.allocateObject_address objectAllocation
  have extension := allocateConstructor_nonempty_prefixExtension state result info fields
    address related.frontier arity nonempty tagFits objectFieldsFit usizeFieldsFit
      scalarBytesFit allocated
  obtain ⟨finalFrontier, objectRelated, exactHeader⟩ :=
    allocateConstructor_nonempty_objectRel state result witness info fieldKinds fields
      semanticFields address related.frontier arity semanticArity fieldKindsSize
      fieldKindsValid fieldRelated nonempty tagFits objectFieldsFit usizeFieldsFit
      scalarBytesFit allocated
  have locationFresh : witness.locations.lookup? runtime.nextLocation = none := by
    cases found : witness.locations.lookup? runtime.nextLocation with
    | none => rfl
    | some oldAddress =>
        exfalso
        obtain ⟨cell, semanticFound, _⟩ :=
          related.concreteToSemantic runtime.nextLocation oldAddress found
        have beforeNext :=
          related.locationsBeforeNext runtime.nextLocation cell semanticFound
        exact (Nat.lt_irrefl runtime.nextLocation) beforeNext
  have descriptorFresh : ∀ old descriptor,
      witness.descriptors.lookup? old = some descriptor →
      address.value ≠ old.value := by
    intro old descriptor found equal
    have owned := related.descriptorsOwned old descriptor found
    simp [headerBytes] at owned
    have addressEq := freshAddress
    omega
  have witnessExtension := witness.bindConstructor_extends runtime.nextLocation address
    info fieldKinds locationFresh descriptorFresh
  have locationAddressFresh : ∀ old oldAddress,
      witness.locations.lookup? old = some oldAddress → oldAddress ≠ address := by
    intro old oldAddress found equal
    obtain ⟨cell, _, cellRelated⟩ :=
      related.concreteToSemantic old oldAddress found
    have owned := cellRelated.headerOwned
    subst oldAddress
    simp [headerBytes] at owned
    have addressEq := freshAddress
    omega
  have promotedAddressFresh : ∀ payload oldAddress,
      witness.promotedTags.Contains payload oldAddress → address ≠ oldAddress := by
    intro payload oldAddress found equal
    have promoted := related.promoted payload oldAddress found
    obtain ⟨header, _, _, _, _, _, extent, payloadFits⟩ := promoted.header
    subst oldAddress
    simp [headerBytes] at payloadFits extent
    have addressEq := freshAddress
    omega
  let header := Header.forAllocation .constructor
    (ConstructorLayout.ofInfo info).allocationBytes false
      (UInt32.ofNat info.cidx) (UInt32.ofNat info.size)
      (UInt32.ofNat info.usize) (UInt32.ofNat info.ssize)
  have headerRead : result.readLiveHeader address = .ok header := by
    simpa [header] using exactHeader
  have headerKind : header.kind = .constructor := rfl
  have headerRefCount : header.refCount.toNat = 1 := rfl
  have headerPersistent : header.persistent = false := rfl
  have addressHeap :=
    (MemoryState.PrefixExtension.readLiveHeader_facts result address header headerRead).1
  have witnessWellFormed := related.witnessWellFormed.bindConstructor
    runtime.nextLocation address info fieldKinds addressHeap locationAddressFresh
      promotedAddressFresh
  have objectRelatedNext := objectRelated.witnessExtension witnessExtension
  obtain ⟨_, rawHeaderRead, _, headerMinimum, headerAligned, _⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts result address header headerRead
  have newExtent :
      address.value + header.allocationBytes.toNat ≤ result.heapCursor := by
    obtain ⟨objectHeader, objectHeaderRead, _, allocationBytes, _, _, _, _, _⟩ :=
      objectRelatedNext.header
    rw [headerRead] at objectHeaderRead
    have headerEq := Except.ok.inj objectHeaderRead
    subst objectHeader
    rw [allocationBytes]
    exact objectRelatedNext.extent
  have newRegion : ∃ newHeader,
      Header.read result.memory address = .ok newHeader ∧
      headerBytes ≤ newHeader.allocationBytes.toNat ∧
      newHeader.allocationBytes.toNat % target.heapAlignment = 0 ∧
      address.value + newHeader.allocationBytes.toNat ≤ result.heapCursor :=
    ⟨header, rawHeaderRead, headerMinimum, headerAligned, newExtent⟩
  obtain ⟨descriptorRegion, descriptorDisjoint⟩ :=
    related.extendDescriptorSpatial extension address freshAddress
      (fun other different =>
        witness.lookup_bindConstructor_descriptor_other runtime.nextLocation address
          other info fieldKinds different)
      newRegion
  have newCellRelated : LiveCellRel result
      (witness.bindConstructor runtime.nextLocation address info fieldKinds) address
      (semanticConstructorCell info semanticFields) := by
    apply LiveCellRel.constructor
      (RefinementWitness.lookup_bindConstructor_descriptor witness runtime.nextLocation
        address info fieldKinds)
      (by rfl) objectRelatedNext headerRead headerKind
    · simpa [semanticConstructorCell] using headerRefCount
    · simpa [semanticConstructorCell] using headerPersistent
    · rfl
  refine ⟨?_, ValueRel.new_constructor_result witness runtime.nextLocation address info
    fieldKinds⟩
  refine {
    frontier := finalFrontier
    witnessWellFormed
    locationsBeforeNext := ?_
    descriptorsOwned := ?_
    descriptorRegion
    descriptorDisjoint
    semanticToConcrete := ?_
    concreteToSemantic := ?_
    promoted := ?_ }
  · intro location cell found
    by_cases isNew : location = runtime.nextLocation
    · subst location
      change runtime.nextLocation < runtime.nextLocation + 1
      exact Nat.lt_succ_self runtime.nextLocation
    · have oldFound : findCell? runtime.heap location = some cell := by
        simpa [semanticConstructorResult, findCell?, isNew, Ne.symm isNew] using found
      have oldBefore := related.locationsBeforeNext location cell oldFound
      change location < runtime.nextLocation + 1
      exact Nat.lt_trans oldBefore (Nat.lt_succ_self runtime.nextLocation)
  · intro other descriptor found
    by_cases isNew : address.value = other.value
    · rw [← isNew]
      exact objectRelatedNext.headerOwned
    · rw [witness.lookup_bindConstructor_descriptor_other runtime.nextLocation address
        other info fieldKinds isNew] at found
      exact Nat.le_trans (related.descriptorsOwned other descriptor found)
        extension.cursor
  · intro location cell found
    by_cases isNew : location = runtime.nextLocation
    · subst location
      have cellEq : cell = semanticConstructorCell info semanticFields := by
        simpa [semanticConstructorResult, findCell?] using found.symm
      subst cell
      exact ⟨address,
        RefinementWitness.lookup_bindConstructor_location witness runtime.nextLocation
          address info fieldKinds,
        .live newCellRelated⟩
    · have oldFound : findCell? runtime.heap location = some cell := by
        simpa [semanticConstructorResult, findCell?, isNew, Ne.symm isNew] using found
      obtain ⟨oldAddress, mapped, cellRelated⟩ :=
        related.semanticToConcrete location cell oldFound
      exact ⟨oldAddress, witnessExtension.locations _ _ mapped,
        (cellRelated.prefixExtension extension).witnessExtension witnessExtension⟩
  · intro location concreteAddress mapped
    by_cases isNew : location = runtime.nextLocation
    · subst location
      simp [RefinementWitness.bindConstructor, LocationMap.lookup?] at mapped
      subst concreteAddress
      exact ⟨semanticConstructorCell info semanticFields,
        by simp [semanticConstructorResult, findCell?], .live newCellRelated⟩
    · rw [witness.lookup_bindConstructor_location_other runtime.nextLocation location
        address info fieldKinds isNew] at mapped
      obtain ⟨cell, oldFound, cellRelated⟩ :=
        related.concreteToSemantic location concreteAddress mapped
      exact ⟨cell, by
          simpa [semanticConstructorResult, findCell?, isNew, Ne.symm isNew],
        (cellRelated.prefixExtension extension).witnessExtension witnessExtension⟩
  · intro payload concreteAddress mapped
    exact ((related.promoted payload concreteAddress mapped).prefixExtension extension)
      |>.witnessExtension witnessExtension

end Fir.Wasm.Concrete
