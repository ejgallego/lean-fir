import Fir.Wasm.Concrete.GlobalCorrectness
import Fir.Wasm.Concrete.OwnershipFrameCorrectness

namespace Fir.Wasm.Concrete

open Fir.LeanIR.Impure

/-- A live header already carrying the persistent bit is an exact no-op for
every concrete persistence fuel budget. -/
theorem markPersistentFuel_eq_of_persistent
    {state : MemoryState} {object : Word32} {header : Header}
    (headerRead : state.readLiveHeader object = .ok header)
    (persistent : header.persistent = true) (fuel : Nat)
    (descriptors : ClosureDescriptorTable := #[]) :
    markPersistentFuel fuel state object descriptors = .ok state := by
  obtain ⟨heap, _, _, _, _, _⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state object header headerRead
  cases fuel with
  | zero =>
      simp only [markPersistentFuel]
      rw [heap]
      simp only [headerRead, liftMemory, Bind.bind, Except.bind]
      rw [if_pos persistent]
      rfl
  | succ fuel =>
      simp only [markPersistentFuel]
      rw [heap]
      simp only [headerRead, liftMemory, Bind.bind, Except.bind]
      rw [if_pos persistent]
      rfl

/-- The public cursor-bounded persistence operation likewise leaves an
already-persistent allocation unchanged. -/
theorem markPersistent_eq_of_persistent
    {state : MemoryState} {object : Word32} {header : Header}
    (headerRead : state.readLiveHeader object = .ok header)
    (persistent : header.persistent = true)
    (descriptors : ClosureDescriptorTable := #[]) :
    markPersistent state object descriptors = .ok state := by
  exact markPersistentFuel_eq_of_persistent headerRead persistent _ descriptors

/-- Marking one represented live cell persistent rewrites only its common
ownership metadata. The returned raw header write is the spatial input needed
to rebuild `LiveHeapRel` around the changed target cell. -/
theorem LiveCellRel.writePersistentMetadata
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : LiveCellRel state witness address cell)
    (valid : state.FrontierInvariant) :
    ∃ result header memory,
      state.readLiveHeader address = .ok header ∧
      writeLiveHeader state address
          { header with refCount := 0, persistent := true } = .ok result ∧
      result = { state with memory } ∧
      ({ header with refCount := 0, persistent := true } : Header).write
          state.memory address = .ok memory ∧
      result.FrontierInvariant ∧
      LiveCellRel result witness address
        { cell with rc := 0, persistent := true } := by
  have commonHeaderOwned := related.headerOwned
  cases related with
  | constructor descriptor objectEq objectRelated headerRead headerKind refCount
        persistent live =>
      obtain ⟨result, updatedHeader, memory, operation, updatedEq, resultEq,
          headerWrite, finalValid, headerAfter⟩ :=
        writeOwnershipMetadata_header valid headerRead objectRelated.headerOwned 0 true
      subst updatedHeader
      obtain ⟨objectResult, objectHeader, objectOperation, objectUpdatedEq,
          _, objectHeaderAfter, objectAfter⟩ :=
        objectRelated.writeOwnershipMetadata headerRead valid 0 true
      subst objectHeader
      rw [operation] at objectOperation
      have objectResultEq := Except.ok.inj objectOperation
      subst objectResult
      let replacement : HeapCell := { cell with rc := 0, persistent := true }
      refine ⟨result, _, memory, headerRead, operation, resultEq, headerWrite,
        finalValid, ?_⟩
      apply LiveCellRel.constructor descriptor (by simpa [replacement] using objectEq)
        objectAfter objectHeaderAfter
      · simpa using headerKind
      · simp
      · simp
      · simpa [replacement] using live
  | boxed descriptor objectEq objectRelated refCount persistent live =>
      obtain ⟨result, updatedHeader, memory, operation, updatedEq, resultEq,
          headerWrite, finalValid, headerAfter⟩ :=
        writeOwnershipMetadata_header valid objectRelated.headerRead
          objectRelated.headerOwned 0 true
      subst updatedHeader
      obtain ⟨objectResult, objectHeader, objectOperation, objectUpdatedEq,
          _, objectHeaderAfter, objectAfter⟩ :=
        objectRelated.writeOwnershipMetadata valid 0 true
      subst objectHeader
      rw [operation] at objectOperation
      have objectResultEq := Except.ok.inj objectOperation
      subst objectResult
      let replacement : HeapCell := { cell with rc := 0, persistent := true }
      refine ⟨result, _, memory, objectRelated.headerRead, operation, resultEq,
        headerWrite, finalValid, ?_⟩
      apply LiveCellRel.boxed descriptor (by simpa [replacement] using objectEq)
        objectAfter
      · simp
      · simp
      · simpa [replacement] using live
  | @natural value header _ descriptor objectEq headerRead headerKind marker extent
        limbsFit decoded refCount persistent live =>
      obtain ⟨result, updatedHeader, memory, operation, updatedEq, resultEq,
          headerWrite, finalValid, headerAfter⟩ :=
        writeOwnershipMetadata_header valid headerRead commonHeaderOwned 0 true
      subst updatedHeader
      subst result
      obtain ⟨heap, _, _, _, _, _⟩ :=
        MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead
      have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
        Nat.le_trans commonHeaderOwned valid.cursorInBounds
      have decoderEq :
          readNatural ({ state with memory } : MemoryState) address =
            readNatural state address := by
        unfold readNatural
        rw [heap]
        simp only
        rw [headerAfter, headerRead]
        simp only [Bind.bind, Except.bind, liftMemory]
        simp [headerKind, marker]
        rw [Header.readNaturalLimbs_of_write_eq_ok state.memory memory address
          { header with refCount := 0, persistent := true }
          0 _ headerInBounds headerWrite]
      let replacement : HeapCell := { cell with rc := 0, persistent := true }
      refine ⟨{ state with memory }, header, memory, headerRead, operation, rfl,
        headerWrite, finalValid, ?_⟩
      apply LiveCellRel.natural descriptor (by simpa [replacement] using objectEq)
        headerAfter
      · simpa using headerKind
      · simpa using marker
      · simpa using extent
      · simpa using limbsFit
      · rw [decoderEq]
        exact decoded
      · simp
      · simp
      · simpa [replacement] using live
  | closure closureRelated =>
      cases closureRelated with
      | closure objectEq objectRelated headerRead headerKind descriptorLookup
          fixedCount extent refCount persistent live =>
          have headerOwned : address.value + headerBytes ≤ state.heapCursor := by
            simp [closureCaptureAddress, target] at extent ⊢
            omega
          obtain ⟨result, updatedHeader, memory, operation, updatedEq, resultEq,
              headerWrite, finalValid, headerAfter⟩ :=
            writeOwnershipMetadata_header valid headerRead headerOwned 0 true
          subst updatedHeader
          obtain ⟨objectResult, objectHeader, objectOperation, objectUpdatedEq,
              _, objectHeaderAfter, cursor, objectAfter⟩ :=
            objectRelated.writeOwnershipMetadata headerRead headerKind descriptorLookup
              fixedCount headerOwned valid 0 true
          subst objectHeader
          rw [operation] at objectOperation
          have objectResultEq := Except.ok.inj objectOperation
          subst objectResult
          let replacement : HeapCell := { cell with rc := 0, persistent := true }
          refine ⟨result, _, memory, headerRead, operation, resultEq, headerWrite,
            finalValid, .closure ?_⟩
          apply ClosureCellRel.closure (by simpa [replacement] using objectEq)
            objectAfter objectHeaderAfter
          · simpa using headerKind
          · simpa using descriptorLookup
          · simpa using fixedCount
          · rw [cursor]
            exact extent
          · simp
          · simp
          · simpa [replacement] using live

/-- The single-node metadata transition rebuilds the complete bidirectional
heap relation, framing every other semantic cell and promoted tag around the
target header write. -/
theorem LiveHeapRel.writePersistentMetadata
    {state : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {address : Word32}
    {cell : HeapCell}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true) :
    ∃ result nextRuntime header,
      state.readLiveHeader address = .ok header ∧
      writeLiveHeader state address
          { header with refCount := 0, persistent := true } = .ok result ∧
      setCell runtime location { cell with rc := 0, persistent := true } =
        .ok nextRuntime ∧
      LiveHeapRel result witness nextRuntime := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  obtain ⟨targetDescriptor, targetDescriptorFound⟩ := targetRelated.descriptor
  obtain ⟨result, header, memory, headerRead, operation, resultEq, headerWrite,
      finalValid, targetAfter⟩ :=
    targetRelated.writePersistentMetadata related.frontier
  obtain ⟨_, rawRead, _, _, _, _⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead
  have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
    Nat.le_trans targetRelated.headerOwned related.frontier.cursorInBounds
  obtain ⟨nextRuntime, semanticUpdate, finalRelated⟩ :=
    related.setCell_of_headerWrite mapped found targetDescriptorFound rawRead resultEq
      headerInBounds headerWrite (by rfl) finalValid (.live targetAfter)
  exact ⟨result, nextRuntime, header, headerRead, operation, semanticUpdate,
    finalRelated⟩

/-- For boxes and heap naturals, the semantic persistence fold has no heap
children, so the fuel-indexed operation is exactly the initial metadata
replacement. -/
theorem markPersistentLocationFuel_leaf_eq
    {heap after : Heap} {location : Location} {cell : HeapCell}
    (found : findCell? heap location = some cell)
    (live : cell.live = true) (ordinary : cell.persistent = false)
    (leafCell :
      (∃ (kind : BoxedScalarKind) (scalar : BoxedScalar),
        cell.object = .boxed kind.semanticType scalar.semanticValue) ∨
      (∃ value : Nat, cell.object = .natural value))
    (replaced : replaceCell heap location
      { cell with rc := 0, persistent := true } = some after)
    (fuel : Nat) :
    markPersistentLocationFuel (fuel + 1) heap location = after := by
  simp only [markPersistentLocationFuel, found]
  rw [if_neg (by simp [live, ordinary])]
  rw [replaced]
  rcases leafCell with boxedCell | naturalCell
  · obtain ⟨kind, scalar, objectEq⟩ := boxedCell
    rw [objectEq]
    cases scalar <;> rfl
  · obtain ⟨value, objectEq⟩ := naturalCell
    rw [objectEq]
    rfl

/-- Positive-fuel concrete persistence and FIR persistence agree for the two
nonrecursive mapped heap representations. This is the first constructive
heap-valued cache boundary; recursive constructors and closures build on the
same metadata transition. -/
theorem LiveHeapRel.markPersistentFuel_refines_leaf
    {state : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {address : Word32}
    {cell : HeapCell} {descriptors : ClosureDescriptorTable}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true) (ordinary : cell.persistent = false)
    (leafCell :
      (∃ (kind : BoxedScalarKind) (scalar : BoxedScalar),
        cell.object = .boxed kind.semanticType scalar.semanticValue) ∨
      (∃ value : Nat, cell.object = .natural value))
    (fuel : Nat) :
    ∃ result,
      markPersistentFuel (fuel + 1) state address descriptors = .ok result ∧
      LiveHeapRel result witness {
        runtime with heap :=
          markPersistentLocationFuel (fuel + 1) runtime.heap location } := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  obtain ⟨result, nextRuntime, header, headerRead, operation, semanticUpdate,
      finalRelated⟩ :=
    related.writePersistentMetadata mapped found live
  unfold setCell at semanticUpdate
  cases replacedEq : replaceCell runtime.heap location
      { cell with rc := 0, persistent := true } with
  | none =>
      rw [replacedEq] at semanticUpdate
      contradiction
  | some after =>
      rw [replacedEq] at semanticUpdate
      have nextRuntimeEq := Except.ok.inj semanticUpdate
      subst nextRuntime
      have semanticHeapEq := markPersistentLocationFuel_leaf_eq found live ordinary
        leafCell replacedEq fuel
      have concreteOperation :
          markPersistentFuel (fuel + 1) state address descriptors = .ok result := by
        cases targetRelated with
        | constructor descriptor objectEq objectRelated targetHeaderRead headerKind
            refCount persistent cellLive =>
            rcases leafCell with boxedCell | naturalCell
            · obtain ⟨kind, scalar, boxedEq⟩ := boxedCell
              rw [objectEq] at boxedEq
              contradiction
            · obtain ⟨value, naturalEq⟩ := naturalCell
              rw [objectEq] at naturalEq
              contradiction
        | @boxed kind scalar targetHeader _ descriptor objectEq objectRelated refCount
            persistent cellLive =>
            rw [objectRelated.headerRead] at headerRead
            have headerEq := Except.ok.inj headerRead
            subst header
            have headerOrdinary : targetHeader.persistent = false :=
              persistent.trans ordinary
            obtain ⟨heap, _, _, _, _, _⟩ :=
              MemoryState.PrefixExtension.readLiveHeader_facts state address _
                objectRelated.headerRead
            have owned : readOwnedReferences state address targetHeader
                descriptors = .ok [] := by
              simp [readOwnedReferences, objectRelated.headerKind]
            simp only [markPersistentFuel]
            rw [heap, objectRelated.headerRead]
            simp only [liftMemory, Bind.bind, Except.bind]
            rw [if_neg (by simp [headerOrdinary])]
            rw [owned]
            rw [operation]
            rfl
        | @natural value targetHeader _ descriptor objectEq targetHeaderRead
            headerKind marker extent limbsFit decoded refCount persistent cellLive =>
            rw [targetHeaderRead] at headerRead
            have headerEq := Except.ok.inj headerRead
            subst header
            have headerOrdinary : targetHeader.persistent = false :=
              persistent.trans ordinary
            obtain ⟨heap, _, _, _, _, _⟩ :=
              MemoryState.PrefixExtension.readLiveHeader_facts state address _
                targetHeaderRead
            have owned : readOwnedReferences state address targetHeader descriptors =
                .ok [] := by
              simp [readOwnedReferences, headerKind]
            simp only [markPersistentFuel]
            rw [heap, targetHeaderRead]
            simp only [liftMemory, Bind.bind, Except.bind]
            rw [if_neg (by simp [headerOrdinary])]
            rw [owned]
            rw [operation]
            rfl
        | closure closureRelated =>
            obtain ⟨function, arity, captures, closureEq⟩ := closureRelated.objectEq
            rcases leafCell with boxedCell | naturalCell
            · obtain ⟨kind, scalar, boxedEq⟩ := boxedCell
              rw [closureEq] at boxedEq
              contradiction
            · obtain ⟨value, naturalEq⟩ := naturalCell
              rw [closureEq] at naturalEq
              contradiction
      refine ⟨result, concreteOperation, ?_⟩
      rw [semanticHeapEq]
      exact finalRelated

/-- Nonrecursive semantic persistence is independent of the positive fuel
budget chosen by the concrete and semantic heap bounds. -/
theorem markPersistentLocationFuel_leaf_fuel_independent
    {heap : Heap} {location : Location} {cell : HeapCell}
    (found : findCell? heap location = some cell)
    (live : cell.live = true) (ordinary : cell.persistent = false)
    (leafCell :
      (∃ (kind : BoxedScalarKind) (scalar : BoxedScalar),
        cell.object = .boxed kind.semanticType scalar.semanticValue) ∨
      (∃ value : Nat, cell.object = .natural value))
    (leftFuel rightFuel : Nat) :
    markPersistentLocationFuel (leftFuel + 1) heap location =
      markPersistentLocationFuel (rightFuel + 1) heap location := by
  obtain ⟨after, post⟩ := replaceCell_spec_of_find heap location cell
    { cell with rc := 0, persistent := true } found
  exact (markPersistentLocationFuel_leaf_eq found live ordinary leafCell
    post.replaced leftFuel).trans
      (markPersistentLocationFuel_leaf_eq found live ordinary leafCell
        post.replaced rightFuel).symm

/-- The public cursor-bounded concrete operation refines FIR's heap-length-
bounded persistence operation for an ordinary box or heap natural. -/
theorem LiveHeapRel.markPersistent_refines_leaf
    {state : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {address : Word32}
    {cell : HeapCell} {descriptors : ClosureDescriptorTable}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true) (ordinary : cell.persistent = false)
    (leafCell :
      (∃ (kind : BoxedScalarKind) (scalar : BoxedScalar),
        cell.object = .boxed kind.semanticType scalar.semanticValue) ∨
      (∃ value : Nat, cell.object = .natural value)) :
    ∃ result,
      markPersistent state address descriptors = .ok result ∧
      LiveHeapRel result witness
        (runtime.markPersistent (.object (.heap location))) := by
  obtain ⟨result, operation, finalRelated⟩ :=
    related.markPersistentFuel_refines_leaf mapped found live ordinary leafCell
      (state.heapCursor / headerBytes)
  have fuelEq := markPersistentLocationFuel_leaf_fuel_independent found live ordinary
    leafCell (state.heapCursor / headerBytes) runtime.heap.length
  refine ⟨result, ?_, ?_⟩
  · exact operation
  · simpa [RuntimeState.markPersistent, fuelEq] using finalRelated

/-- An ordinary mapped box or heap natural constructively discharges the
cache-persistence boundary. -/
theorem CachePersistenceRefines.of_heapLeaf
    {concrete : MemoryState} {witness : RefinementWitness}
    {semantic : RuntimeState} {kind : AbiKind} {lane : LaneValue}
    {location : Location} {cell : HeapCell}
    {descriptors : ClosureDescriptorTable}
    (heapRelated : LiveHeapRel concrete witness semantic)
    (valueRelated : ValueRel witness kind lane (.object (.heap location)))
    (found : findCell? semantic.heap location = some cell)
    (live : cell.live = true) (ordinary : cell.persistent = false)
    (leafCell :
      (∃ (boxedKind : BoxedScalarKind) (scalar : BoxedScalar),
        cell.object = .boxed boxedKind.semanticType scalar.semanticValue) ∨
      (∃ value : Nat, cell.object = .natural value)) :
    CachePersistenceRefines concrete witness semantic kind lane
      (.object (.heap location)) descriptors := by
  cases valueRelated with
  | object related =>
      cases related with
      | mapped mapped =>
          obtain ⟨result, operation, finalRelated⟩ :=
            heapRelated.markPersistent_refines_leaf mapped found live ordinary leafCell
          exact ⟨result, operation, finalRelated⟩
  | tobject related =>
      cases related with
      | heap related =>
          cases related with
          | mapped mapped =>
              obtain ⟨result, operation, finalRelated⟩ :=
                heapRelated.markPersistent_refines_leaf mapped found live ordinary
                  leafCell
              exact ⟨result, operation, finalRelated⟩

/-- Syntactic classification used by cache composition: only a semantic heap
reference requires the recursive persistence simulation. -/
def IsNonHeapReference : Value → Prop
  | .object (.heap _) => False
  | _ => True

/-- Every cache lane that does not denote a semantic heap location discharges
the persistence boundary constructively. Scalar and sentinel lanes bypass the
concrete operation; direct tags are immediate no-ops; promoted tags are
already persistent by their representation invariant. -/
theorem CachePersistenceRefines.of_nonHeapReference
    {concrete : MemoryState} {witness : RefinementWitness}
    {semantic : RuntimeState} {kind : AbiKind} {lane : LaneValue}
    {value : Value} {descriptors : ClosureDescriptorTable}
    (heapRelated : LiveHeapRel concrete witness semantic)
    (valueRelated : ValueRel witness kind lane value)
    (nonHeap : IsNonHeapReference value) :
    CachePersistenceRefines concrete witness semantic kind lane value descriptors := by
  cases valueRelated with
  | object related => contradiction
  | tagged related =>
      cases related with
      | immediate payload fits =>
          refine ⟨concrete, ?_, ?_⟩
          · simp [persistGlobalValue, markPersistent, markPersistentFuel,
              Word32.classify_encodeImmediate]
            rfl
          · simpa [RuntimeState.markPersistent] using heapRelated
      | promoted found =>
          obtain ⟨header, headerRead, _, persistent, _, _, _, _⟩ :=
            (heapRelated.promoted _ _ found).header
          refine ⟨concrete, ?_, ?_⟩
          · simp only [persistGlobalValue]
            exact markPersistent_eq_of_persistent headerRead persistent descriptors
          · simpa [RuntimeState.markPersistent] using heapRelated
  | tobject related =>
      cases related with
      | heap related => contradiction
      | tagged related =>
          cases related with
          | immediate payload fits =>
              refine ⟨concrete, ?_, ?_⟩
              · simp [persistGlobalValue, markPersistent, markPersistentFuel,
                  Word32.classify_encodeImmediate]
                rfl
              · simpa [RuntimeState.markPersistent] using heapRelated
          | promoted found =>
              obtain ⟨header, headerRead, _, persistent, _, _, _, _⟩ :=
                (heapRelated.promoted _ _ found).header
              refine ⟨concrete, ?_, ?_⟩
              · simp only [persistGlobalValue]
                exact markPersistent_eq_of_persistent headerRead persistent descriptors
              · simpa [RuntimeState.markPersistent] using heapRelated
  | erased =>
      exact ⟨concrete, by simp [persistGlobalValue]; rfl,
        by simpa [RuntimeState.markPersistent] using heapRelated⟩
  | reuseNone =>
      exact ⟨concrete, by simp [persistGlobalValue]; rfl,
        by simpa [RuntimeState.markPersistent] using heapRelated⟩
  | reuseSome related =>
      exact ⟨concrete, by simp [persistGlobalValue]; rfl,
        by simpa [RuntimeState.markPersistent] using heapRelated⟩
  | uint8 encoded =>
      exact ⟨concrete, by simp [persistGlobalValue]; rfl,
        by simpa [RuntimeState.markPersistent] using heapRelated⟩
  | uint16 encoded =>
      exact ⟨concrete, by simp [persistGlobalValue]; rfl,
        by simpa [RuntimeState.markPersistent] using heapRelated⟩
  | uint32 encoded =>
      exact ⟨concrete, by simp [persistGlobalValue]; rfl,
        by simpa [RuntimeState.markPersistent] using heapRelated⟩
  | uint64 =>
      exact ⟨concrete, by simp [persistGlobalValue]; rfl,
        by simpa [RuntimeState.markPersistent] using heapRelated⟩
  | usize =>
      exact ⟨concrete, by simp [persistGlobalValue]; rfl,
        by simpa [RuntimeState.markPersistent] using heapRelated⟩

/-- Cache writes of non-heap values no longer require callers to manufacture
an explicit persistence witness. -/
theorem ConcreteRuntimeRel.writeGlobal_nonHeapReference
    {concrete : ConcreteRuntimeState} {witness : RefinementWitness}
    {semantic : RuntimeState} {name : Lean.Name} {slot : ConcreteGlobalSlot}
    {kind : AbiKind} {lane : LaneValue} {value : Value}
    {descriptors : ClosureDescriptorTable}
    (related : ConcreteRuntimeRel concrete witness semantic)
    (found : concrete.globals.find? name = some slot)
    (kindEq : slot.kind = kind)
    (valueRelated : ValueRel witness kind lane value)
    (nonHeap : IsNonHeapReference value) :
    ∃ after,
      concrete.writeGlobal name kind lane descriptors = .ok after ∧
        ConcreteRuntimeRel after witness (semantic.setGlobal name value) := by
  exact related.writeGlobal found kindEq valueRelated
    (.of_nonHeapReference related.heap valueRelated nonHeap)

/-- Cache writes of ordinary mapped boxes and heap naturals also obtain their
persistence witness from the heap relation itself. -/
theorem ConcreteRuntimeRel.writeGlobal_heapLeaf
    {concrete : ConcreteRuntimeState} {witness : RefinementWitness}
    {semantic : RuntimeState} {name : Lean.Name} {slot : ConcreteGlobalSlot}
    {kind : AbiKind} {lane : LaneValue} {location : Location} {cell : HeapCell}
    {descriptors : ClosureDescriptorTable}
    (related : ConcreteRuntimeRel concrete witness semantic)
    (globalFound : concrete.globals.find? name = some slot)
    (kindEq : slot.kind = kind)
    (valueRelated :
      ValueRel witness kind lane (.object (.heap location)))
    (cellFound : findCell? semantic.heap location = some cell)
    (live : cell.live = true) (ordinary : cell.persistent = false)
    (leafCell :
      (∃ (boxedKind : BoxedScalarKind) (scalar : BoxedScalar),
        cell.object = .boxed boxedKind.semanticType scalar.semanticValue) ∨
      (∃ value : Nat, cell.object = .natural value)) :
    ∃ after,
      concrete.writeGlobal name kind lane descriptors = .ok after ∧
        ConcreteRuntimeRel after witness
          (semantic.setGlobal name (.object (.heap location))) := by
  exact related.writeGlobal globalFound kindEq valueRelated
    (.of_heapLeaf related.heap valueRelated cellFound live ordinary leafCell)

end Fir.Wasm.Concrete
