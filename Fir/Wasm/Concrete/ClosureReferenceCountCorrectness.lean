import Fir.Wasm.Concrete.ClosureOwnershipCorrectness

namespace Fir.Wasm.Concrete

open Fir.LeanIR.Impure

/-- Rewriting only a closure's reference count preserves its immutable module
metadata and every typed capture slot. -/
theorem ClosureObjectRel.writeReferenceCount
    {state : MemoryState} {witness : RefinementWitness} {address : Word32}
    {function : Lean.Name} {arity : Nat} {captureKinds : Array AbiKind}
    {captures : Array Value} {header : Header}
    (related : ClosureObjectRel state witness witness.closureDispatch
      witness.closureDescriptors address function arity captureKinds captures)
    (headerRead : state.readLiveHeader address = .ok header)
    (headerKind : header.kind = .closure)
    (descriptorLookup : witness.closureDescriptors.lookup? header.aux3 =
      some captureKinds)
    (fixedCount : header.aux2.toNat = captures.size)
    (headerOwned : address.value + headerBytes ≤ state.heapCursor)
    (valid : state.FrontierInvariant) (nextCount : UInt32) :
    ∃ result updatedHeader,
      writeLiveHeader state address updatedHeader = .ok result ∧
      updatedHeader = { header with refCount := nextCount } ∧
      result.FrontierInvariant ∧
      result.readLiveHeader address = .ok updatedHeader ∧
      result.heapCursor = state.heapCursor ∧
      ClosureObjectRel result witness witness.closureDispatch
        witness.closureDescriptors address function arity captureKinds captures := by
  obtain ⟨metadata, metadataRead, metadataFunction, metadataArity,
      metadataFixed, metadataKinds⟩ := related.metadata
  have heap :=
    (MemoryState.PrefixExtension.readLiveHeader_facts state address header
      headerRead).1
  have closureHeaderSuccess : ∃ decoded,
      readClosureHeader state address = .ok decoded := by
    cases result : readClosureHeader state address with
    | error failure =>
        unfold readClosureMetadata at metadataRead
        simp only [result, Bind.bind, Except.bind] at metadataRead
        contradiction
    | ok decoded => exact ⟨decoded, rfl⟩
  obtain ⟨decoded, decodedRead⟩ := closureHeaderSuccess
  have decodedEq : decoded = header := by
    have check := decodedRead
    unfold readClosureHeader at check
    simp only [heap, if_true] at check
    rw [headerRead] at check
    simp only [liftMemory, Bind.bind, Except.bind] at check
    split at check <;> split at check
    · simpa using (Except.ok.inj check).symm
    · contradiction
    · contradiction
    · contradiction
  subst decoded
  have kindCheck : (header.kind == ObjectKind.closure) = true := by
    rw [headerKind]
    decide
  have validation : header.aux2.toNat < header.aux1.toNat ∧
      align8 (headerBytes + target.semanticSlotBytes * header.aux2.toNat) ≤
        header.allocationBytes.toNat := by
    have check := decodedRead
    unfold readClosureHeader at check
    simp only [heap, if_true] at check
    rw [headerRead] at check
    simp only [liftMemory, Bind.bind, Except.bind] at check
    rw [kindCheck] at check
    simp only [if_true] at check
    split at check
    · rename_i validCheck
      simpa using validCheck
    · contradiction
  have captureSize : captureKinds.size = header.aux2.toNat := by
    exact related.captureKindsSize.trans fixedCount.symm
  have targetLookup : ClosureDispatchTable.lookup? witness.closureDispatch
      header.aux0 = some function := by
    unfold readClosureMetadata at metadataRead
    rw [decodedRead] at metadataRead
    simp only [Bind.bind, Except.bind] at metadataRead
    cases targetResult : ClosureDispatchTable.lookup? witness.closureDispatch
        header.aux0 with
    | none =>
        simp [targetResult] at metadataRead
    | some foundFunction =>
        rw [targetResult, descriptorLookup] at metadataRead
        simp [captureSize] at metadataRead
        have metadataEq := Except.ok.inj metadataRead
        have foundEq : foundFunction = function := by
          calc
            foundFunction = metadata.function := by
              simpa using congrArg ClosureMetadata.function metadataEq
            _ = function := metadataFunction
        subst foundFunction
        rfl
  have headerArity : header.aux1.toNat = arity := by
    unfold readClosureMetadata at metadataRead
    rw [decodedRead] at metadataRead
    simp only [Bind.bind, Except.bind] at metadataRead
    rw [targetLookup, descriptorLookup] at metadataRead
    simp [captureSize] at metadataRead
    have metadataEq := Except.ok.inj metadataRead
    calc
      header.aux1.toNat = metadata.arity := by
        simpa using congrArg ClosureMetadata.arity metadataEq
      _ = arity := metadataArity
  obtain ⟨result, updatedHeader, memory, operation, updatedEq, resultEq,
      headerWrite, finalValid, headerReadAfter⟩ :=
    writeReferenceCount_header valid headerRead headerOwned nextCount
  subst updatedHeader
  subst result
  let updatedHeader : Header := { header with refCount := nextCount }
  have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
    Nat.le_trans headerOwned valid.cursorInBounds
  have closureHeaderAfter :
      readClosureHeader ({ state with memory } : MemoryState) address =
        .ok updatedHeader := by
    unfold readClosureHeader
    simp [heap, headerReadAfter, liftMemory, updatedHeader, headerKind]
    simp only [Bind.bind, Except.bind]
    simp [validation]
    rw [show (ObjectKind.closure == ObjectKind.closure) = true by decide]
    rfl
  let metadataAfter : ClosureMetadata := {
    header := updatedHeader
    targetId := updatedHeader.aux0
    descriptorId := updatedHeader.aux3
    function
    arity
    fixed := captures.size
    captureKinds }
  have metadataReadAfter :
      readClosureMetadata ({ state with memory } : MemoryState)
          witness.closureDispatch witness.closureDescriptors address =
        .ok metadataAfter := by
    unfold readClosureMetadata
    rw [closureHeaderAfter]
    simp only [Bind.bind, Except.bind]
    simp [updatedHeader, targetLookup, descriptorLookup, captureSize,
      headerArity, fixedCount, metadataAfter]
    rfl
  have capturesAfter : ∀ index kind value,
      captureKinds[index]? = some kind →
      captures[index]? = some value →
      ∃ lane,
        memory.readClosureCapture
            (closureCaptureAddress address.value index) kind = .ok lane ∧
          ValueRel witness kind lane value := by
    intro index kind value kindAt valueAt
    obtain ⟨lane, readBefore, laneRelated⟩ :=
      related.captures index kind value kindAt valueAt
    refine ⟨lane, ?_, laneRelated⟩
    rw [LinearMemory.readClosureCapture_of_byteFrame state.memory memory
      (closureCaptureAddress address.value index) kind]
    · exact readBefore
    · intro offset offsetLt
      apply Header.readByte_of_write_eq_ok_other state.memory memory address
        { header with refCount := nextCount }
          (closureCaptureAddress address.value index + offset) headerInBounds
            headerWrite
      right
      change address.value + headerBytes ≤
        address.value + headerBytes + target.semanticSlotBytes * index + offset
      exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  refine ⟨{ state with memory }, updatedHeader, operation, rfl, finalValid,
    headerReadAfter, rfl, ?_⟩
  exact {
    descriptor := related.descriptor
    metadata := ⟨metadataAfter, metadataReadAfter, rfl, rfl, rfl, rfl⟩
    captureKindsSize := related.captureKindsSize
    captures := capturesAfter }

/-- Incrementing an ordinary closure changes only its common-header count;
module metadata, captures, and the semantic closure stay related. -/
theorem ClosureCellRel.incrementReference
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : ClosureCellRel state witness address cell)
    (valid : state.FrontierInvariant)
    (amount : Nat) (fits : cell.rc + amount < UInt32.size) (check : Bool) :
    ∃ result,
      Fir.Wasm.Concrete.incrementReference state address amount check = .ok result ∧
      result.FrontierInvariant ∧
      ClosureCellRel result witness address { cell with rc := cell.rc + amount } := by
  have headerOwned := related.headerOwned
  cases related with
  | @closure function arity captureKinds captures header _ objectEq objectRelated
      headerRead headerKind descriptorLookup ordinary fixedCount extent refCount
      persistent live =>
      obtain ⟨result, updatedHeader, write, updatedEq, finalValid,
          headerReadAfter, cursorEq, objectAfter⟩ :=
        objectRelated.writeReferenceCount headerRead headerKind descriptorLookup
          fixedCount headerOwned valid (UInt32.ofNat (cell.rc + amount))
      have heap :=
        (MemoryState.PrefixExtension.readLiveHeader_facts state address header
          headerRead).1
      have notPromoted : header.isPromotedTag = false := by
        have different : (ObjectKind.closure == ObjectKind.natural) = false := by
          decide
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
        rw [uint32Field_eq_ok "reference count" (cell.rc + amount) fits]
        simpa [updatedEq] using write
      subst updatedHeader
      refine ⟨result, operation, finalValid, ?_⟩
      exact .closure (by simpa using objectEq) objectAfter headerReadAfter
        (by simpa using headerKind) (by simpa using descriptorLookup)
        (by simpa using ordinary) (by simpa using fixedCount)
        (by rw [cursorEq]; exact extent)
        (by
          simp only
          exact UInt32.toNat_ofNat_of_lt' fits)
        (by simpa using persistent) (by simpa using live)

/-- Above one, decrementing a closure is nonrecursive and preserves all
closure metadata and captures while lowering both counts by one. -/
theorem ClosureCellRel.decrementReferenceOnce_above_one
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : ClosureCellRel state witness address cell)
    (valid : state.FrontierInvariant) (oneLt : 1 < cell.rc) (check : Bool) :
    ∃ result,
      decrementReferenceOnce state address check = .ok result ∧
      result.FrontierInvariant ∧
      ClosureCellRel result witness address { cell with rc := cell.rc - 1 } := by
  have headerOwned := related.headerOwned
  cases related with
  | @closure function arity captureKinds captures header _ objectEq objectRelated
      headerRead headerKind descriptorLookup ordinary fixedCount extent refCount
      persistent live =>
      obtain ⟨result, updatedHeader, write, updatedEq, finalValid,
          headerReadAfter, cursorEq, objectAfter⟩ :=
        objectRelated.writeReferenceCount headerRead headerKind descriptorLookup
          fixedCount headerOwned valid (UInt32.ofNat (cell.rc - 1))
      have heap :=
        (MemoryState.PrefixExtension.readLiveHeader_facts state address header
          headerRead).1
      have notPromoted : header.isPromotedTag = false := by
        have different : (ObjectKind.closure == ObjectKind.natural) = false := by
          decide
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
      have nextFits : cell.rc - 1 < UInt32.size := by
        have oldFits := UInt32.toNat_lt_size header.refCount
        rw [refCount] at oldFits
        omega
      subst updatedHeader
      refine ⟨result, operation, finalValid, ?_⟩
      exact .closure (by simpa using objectEq) objectAfter headerReadAfter
        (by simpa using headerKind) (by simpa using descriptorLookup)
        (by simpa using ordinary) (by simpa using fixedCount)
        (by rw [cursorEq]; exact extent)
        (by
          simp only
          exact UInt32.toNat_ofNat_of_lt' nextFits)
        (by simpa using persistent) (by simpa using live)

end Fir.Wasm.Concrete
