import Fir.Wasm.Concrete.SharingCorrectness
import Fir.Wasm.Concrete.HeaderCorrectness
import Fir.Wasm.Concrete.ConstructorAllocationCorrectness

namespace Fir.Wasm.Concrete

open Fir.LeanIR.Impure

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
