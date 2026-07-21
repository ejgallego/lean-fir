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

/-- Thread one semantic persistence child step through a full runtime state;
only the heap changes. -/
def markPersistentValueFuel (fuel : Nat) (runtime : RuntimeState) :
    Value → RuntimeState
  | .object (.heap location) =>
      { runtime with heap :=
          markPersistentLocationFuel fuel runtime.heap location }
  | _ => runtime

/-- Both physical tagged encodings are exact concrete persistence no-ops at
every fuel budget. -/
theorem LiveHeapRel.markPersistentFuel_tagged
    {state : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {payload : UInt64} {word : Word32}
    (related : LiveHeapRel state witness runtime)
    (tagged : TaggedReferenceRel witness word payload) (fuel : Nat)
    (descriptors : ClosureDescriptorTable := #[]) :
    markPersistentFuel fuel state word descriptors = .ok state := by
  cases tagged with
  | immediate actualPayload fits =>
      cases fuel <;>
        simp [markPersistentFuel, Word32.classify_encodeImmediate] <;> rfl
  | promoted found =>
      obtain ⟨header, headerRead, _, persistent, _, _, _, _⟩ :=
        (related.promoted payload word found).header
      exact markPersistentFuel_eq_of_persistent headerRead persistent fuel descriptors

/-- One ABI-admissible ownership slot is either a mapped heap child or an
exact concrete/semantic persistence no-op. -/
theorem OwnershipValueRel.persistenceStep
    {state : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {word : Word32} {value : Value}
    (heap : LiveHeapRel state witness runtime)
    (ownership : OwnershipValueRel witness word value) (fuel : Nat)
    (descriptors : ClosureDescriptorTable := #[]) :
    (∃ location,
      value = .object (.heap location) ∧
      witness.locations.lookup? location = some word) ∨
    (markPersistentFuel fuel state word descriptors = .ok state ∧
      markPersistentValueFuel fuel runtime value = runtime) := by
  cases ownership with
  | intro kind admissible valueRelated =>
      cases valueRelated with
      | object heapRelated =>
          cases heapRelated with
          | mapped found => exact .inl ⟨_, rfl, found⟩
      | tagged taggedRelated =>
          exact .inr ⟨heap.markPersistentFuel_tagged taggedRelated fuel descriptors, rfl⟩
      | tobject objectRelated =>
          cases objectRelated with
          | heap heapRelated =>
              cases heapRelated with
              | mapped found => exact .inl ⟨_, rfl, found⟩
          | tagged taggedRelated =>
              exact .inr
                ⟨heap.markPersistentFuel_tagged taggedRelated fuel descriptors, rfl⟩
      | erased =>
          refine .inr ⟨?_, rfl⟩
          cases fuel <;>
            simp [markPersistentFuel, Word32.classify, Word32.zero] <;> rfl
      | reuseNone | reuseSome | uint8 | uint16 | uint32 =>
          simp [AbiKind.isObjectField] at admissible

/-- Ordered ownership correspondence lifts any correct recursive persistence
step through the complete concrete and semantic child folds. -/
theorem OwnershipValuesRel.foldlM_markPersistent_refines
    {state : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {words : List Word32} {values : List Value}
    {fuel : Nat} {descriptors : ClosureDescriptorTable}
    (related : OwnershipValuesRel witness words values)
    (heap : LiveHeapRel state witness runtime)
    (recurse : ∀ {before : MemoryState} {semantic : RuntimeState}
        {location : Location} {address : Word32},
      LiveHeapRel before witness semantic →
      witness.locations.lookup? location = some address →
      ∃ after,
        markPersistentFuel fuel before address descriptors = .ok after ∧
        LiveHeapRel after witness
          (markPersistentValueFuel fuel semantic (.object (.heap location)))) :
    ∃ finalState,
      words.foldlM (init := state) (fun next child =>
        markPersistentFuel fuel next child descriptors) = .ok finalState ∧
      LiveHeapRel finalState witness
        (values.foldl (init := runtime) (markPersistentValueFuel fuel)) := by
  induction related generalizing state runtime with
  | nil =>
      exact ⟨state, rfl, heap⟩
  | @cons word value words values head tail ih =>
      rcases head.persistenceStep heap fuel descriptors with heapStep | noOpStep
      · obtain ⟨location, valueEq, mapped⟩ := heapStep
        subst value
        obtain ⟨nextState, concreteHead, nextHeap⟩ := recurse heap mapped
        obtain ⟨finalState, concreteTail, finalHeap⟩ := ih nextHeap
        refine ⟨finalState, ?_, finalHeap⟩
        simp only [List.foldlM_cons, Bind.bind, Except.bind]
        rw [concreteHead]
        exact concreteTail
      · obtain ⟨concreteHead, semanticHead⟩ := noOpStep
        obtain ⟨finalState, concreteTail, finalHeap⟩ := ih heap
        refine ⟨finalState, ?_, ?_⟩
        · simp only [List.foldlM_cons, Bind.bind, Except.bind]
          rw [concreteHead]
          exact concreteTail
        · simpa [semanticHead] using finalHeap

/-- Runtime-state threading of semantic persistence is exactly the underlying
heap fold, with every auxiliary runtime component framed. -/
theorem foldl_markPersistentValueFuel
    (fuel : Nat) (runtime : RuntimeState) (values : List Value) :
    values.foldl (init := runtime) (markPersistentValueFuel fuel) = {
      runtime with heap :=
        values.foldl (init := runtime.heap) fun heap value =>
          match value with
          | .object (.heap location) =>
              markPersistentLocationFuel fuel heap location
          | _ => heap } := by
  induction values generalizing runtime with
  | nil => rfl
  | cons value values ih =>
      simp only [List.foldl_cons]
      rw [ih]
      cases value with
      | object reference => cases reference <;> rfl
      | usize | scalar | erased | reuseToken => rfl

/-- One ordinary constructor node plus any correct child recursion composes
to the matching positive-fuel persistence step for the complete constructor
subgraph. -/
theorem LiveHeapRel.markPersistentFuel_refines_constructor_step
    {state : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {address : Word32}
    {cell : HeapCell} {semantic : ConstructorObject}
    {descriptors : ClosureDescriptorTable} {fuel : Nat}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true) (ordinary : cell.persistent = false)
    (objectEq : cell.object = .ctor semantic)
    (recurse : ∀ {before : MemoryState} {semanticState : RuntimeState}
        {childLocation : Location} {childAddress : Word32},
      LiveHeapRel before witness semanticState →
      witness.locations.lookup? childLocation = some childAddress →
      ∃ after,
        markPersistentFuel fuel before childAddress descriptors = .ok after ∧
        LiveHeapRel after witness
          (markPersistentValueFuel fuel semanticState
            (.object (.heap childLocation)))) :
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
  cases targetRelated with
  | @constructor info fieldKinds storedSemantic header _ descriptor storedObjectEq
        objectRelated headerRead headerKind refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      have semanticEq := HeapObject.ctor.inj storedObjectEq
      subst storedSemantic
      obtain ⟨words, ownedRead, ownershipRelated⟩ :=
        objectRelated.readOwnedReferences headerRead
      obtain ⟨parentState, parentRuntime, targetHeader, targetHeaderRead,
          parentWrite, semanticUpdate, parentRelated⟩ :=
        related.writePersistentMetadata mapped found live
      rw [headerRead] at targetHeaderRead
      have targetHeaderEq := Except.ok.inj targetHeaderRead
      subst targetHeader
      unfold setCell at semanticUpdate
      cases replacedEq : replaceCell runtime.heap location
          { cell with rc := 0, persistent := true } with
      | none =>
          rw [replacedEq] at semanticUpdate
          contradiction
      | some parentHeap =>
          rw [replacedEq] at semanticUpdate
          have parentRuntimeEq := Except.ok.inj semanticUpdate
          subst parentRuntime
          obtain ⟨result, concreteFold, finalRelated⟩ :=
            ownershipRelated.foldlM_markPersistent_refines parentRelated recurse
          have rootHeapEq :
              markPersistentLocationFuel (fuel + 1) runtime.heap location =
                semantic.objectFields.toList.foldl (init := parentHeap)
                  (fun heap value =>
                    match value with
                    | .object (.heap child) =>
                        markPersistentLocationFuel fuel heap child
                    | _ => heap) := by
            simp only [markPersistentLocationFuel, found]
            rw [if_neg (by simp [live, ordinary])]
            rw [replacedEq, objectEq]
            simp only [HeapObject.ownedValues]
            rw [← Array.foldl_toList]
            rfl
          have addressHeap :=
            (MemoryState.PrefixExtension.readLiveHeader_facts state address header
              headerRead).1
          have headerOrdinary : header.persistent = false :=
            persistent.trans ordinary
          have ownedWithDescriptors :
              readOwnedReferences state address header descriptors = .ok words := by
            simpa [readOwnedReferences, headerKind] using ownedRead
          have concreteOperation :
              markPersistentFuel (fuel + 1) state address descriptors =
                .ok result := by
            simp only [markPersistentFuel]
            rw [addressHeap, headerRead]
            simp only [liftMemory, Bind.bind, Except.bind]
            rw [if_neg (by simp [headerOrdinary])]
            rw [ownedWithDescriptors, parentWrite]
            exact concreteFold
          refine ⟨result, concreteOperation, ?_⟩
          rw [foldl_markPersistentValueFuel] at finalRelated
          simpa [rootHeapEq] using finalRelated
  | boxed descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | natural descriptor storedObjectEq headerRead headerKind marker extent limbsFit
        decoded refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | closure closureRelated =>
      obtain ⟨function, arity, captures, storedObjectEq⟩ := closureRelated.objectEq
      rw [objectEq] at storedObjectEq
      contradiction

/-- A statically non-owning closure capture cannot denote a semantic heap
reference, so persistence is the identity on it. -/
private theorem ValueRel.markPersistentNoOp_of_notObjectField
    {witness : RefinementWitness} {kind : AbiKind} {lane : LaneValue}
    {value : Value} (related : ValueRel witness kind lane value)
    (rejected : kind.isObjectField = false) (fuel : Nat)
    (runtime : RuntimeState) :
    markPersistentValueFuel fuel runtime value = runtime := by
  cases related with
  | object | tagged | tobject | erased =>
      simp [AbiKind.isObjectField] at rejected
  | reuseNone | reuseSome | uint8 | uint16 | uint32 | uint64 | usize => rfl

/-- Filtering statically non-owning closure captures preserves the pure
semantic persistence fold. -/
private theorem closureOwnedValues_foldl_markPersistent_eq_of_each
    (witness : RefinementWitness) (kinds : List AbiKind) (values : List Value)
    (sizeEq : kinds.length = values.length)
    (each : ∀ (offset : Nat) (kind : AbiKind) (value : Value),
      kinds[offset]? = some kind →
      values[offset]? = some value →
      ∃ lane, ValueRel witness kind lane value)
    (fuel : Nat) (runtime : RuntimeState) :
    values.foldl (init := runtime) (markPersistentValueFuel fuel) =
      (closureOwnedValues kinds values).foldl (init := runtime)
        (markPersistentValueFuel fuel) := by
  induction kinds generalizing values runtime with
  | nil =>
      cases values with
      | nil => rfl
      | cons value values => simp at sizeEq
  | cons kind kinds ih =>
      cases values with
      | nil => simp at sizeEq
      | cons value values =>
          have tailSize : kinds.length = values.length := by
            simpa using sizeEq
          obtain ⟨lane, headRelated⟩ := each 0 kind value (by simp) (by simp)
          have tailEach : ∀ (offset : Nat) (tailKind : AbiKind)
              (tailValue : Value),
              kinds[offset]? = some tailKind →
              values[offset]? = some tailValue →
              ∃ lane, ValueRel witness tailKind lane tailValue := by
            intro offset tailKind tailValue kindAt valueAt
            exact each (offset + 1) tailKind tailValue (by simpa using kindAt)
              (by simpa using valueAt)
          by_cases admissible : kind.isObjectField = true
          · simp only [closureOwnedValues, admissible, if_true, List.foldl_cons]
            exact ih values tailSize tailEach
              (markPersistentValueFuel fuel runtime value)
          · have rejected : kind.isObjectField = false := by
              cases found : kind.isObjectField <;> simp_all
            have headNoOp :=
              headRelated.markPersistentNoOp_of_notObjectField rejected fuel runtime
            simp only [closureOwnedValues, rejected, List.foldl_cons]
            rw [headNoOp]
            exact ih values tailSize tailEach runtime

/-- The semantic persistence fold over every closure capture agrees with the
concrete ownership decoder's filtered capture order. -/
theorem ClosureObjectRel.foldl_markPersistent_closureOwnedValues
    {state : MemoryState} {witness : RefinementWitness}
    {dispatch : ClosureDispatchTable} {descriptors : ClosureDescriptorTable}
    {address : Word32} {function : Lean.Name} {arity : Nat}
    {captureKinds : Array AbiKind} {captures : Array Value}
    (related : ClosureObjectRel state witness dispatch descriptors address
      function arity captureKinds captures)
    (fuel : Nat) (runtime : RuntimeState) :
    captures.toList.foldl (init := runtime) (markPersistentValueFuel fuel) =
      (closureOwnedValues captureKinds.toList captures.toList).foldl
        (init := runtime) (markPersistentValueFuel fuel) := by
  apply closureOwnedValues_foldl_markPersistent_eq_of_each witness
    captureKinds.toList captures.toList
  · simpa using related.captureKindsSize
  · intro offset kind value kindAt valueAt
    obtain ⟨lane, _, laneRelated⟩ := related.captures offset kind value
      (by simpa using kindAt) (by simpa using valueAt)
    exact ⟨lane, laneRelated⟩

/-- One ordinary closure node plus any correct child recursion composes to the
matching positive-fuel persistence step. Scalar captures are removed by the
concrete descriptor filter and reinserted through their proved semantic no-op. -/
theorem LiveHeapRel.markPersistentFuel_refines_closure_step
    {state : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {address : Word32}
    {cell : HeapCell} {function : Lean.Name} {arity : Nat}
    {captures : Array Value} {descriptors : ClosureDescriptorTable} {fuel : Nat}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true) (ordinary : cell.persistent = false)
    (objectEq : cell.object = .closure function arity captures)
    (descriptorsEq : descriptors = witness.closureDescriptors)
    (recurse : ∀ {before : MemoryState} {semanticState : RuntimeState}
        {childLocation : Location} {childAddress : Word32},
      LiveHeapRel before witness semanticState →
      witness.locations.lookup? childLocation = some childAddress →
      ∃ after,
        markPersistentFuel fuel before childAddress descriptors = .ok after ∧
        LiveHeapRel after witness
          (markPersistentValueFuel fuel semanticState
            (.object (.heap childLocation)))) :
    ∃ result,
      markPersistentFuel (fuel + 1) state address descriptors = .ok result ∧
      LiveHeapRel result witness {
        runtime with heap :=
          markPersistentLocationFuel (fuel + 1) runtime.heap location } := by
  subst descriptors
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  cases targetRelated with
  | constructor descriptor storedObjectEq objectRelated headerRead headerKind refCount
        persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | boxed descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | natural descriptor storedObjectEq headerRead headerKind marker extent limbsFit
        decoded refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | closure closureRelated =>
      cases closureRelated with
      | @closure storedFunction storedArity captureKinds storedCaptures header _
          storedObjectEq objectRelated headerRead headerKind descriptorLookup fixedCount
          extent refCount persistent cellLive =>
          rw [objectEq] at storedObjectEq
          have closureEq := HeapObject.closure.inj storedObjectEq
          obtain ⟨functionEq, arityEq, capturesEq⟩ := closureEq
          subst storedFunction
          subst storedArity
          subst storedCaptures
          obtain ⟨words, closureWordsRead, ownershipRelated⟩ :=
            objectRelated.readClosureOwnedReferences
          have ownedRead :
              readOwnedReferences state address header witness.closureDescriptors =
                .ok words := by
            simpa [readOwnedReferences, headerKind, descriptorLookup,
              objectRelated.captureKindsSize, fixedCount] using closureWordsRead
          obtain ⟨parentState, parentRuntime, targetHeader, targetHeaderRead,
              parentWrite, semanticUpdate, parentRelated⟩ :=
            related.writePersistentMetadata mapped found live
          rw [headerRead] at targetHeaderRead
          have targetHeaderEq := Except.ok.inj targetHeaderRead
          subst targetHeader
          unfold setCell at semanticUpdate
          cases replacedEq : replaceCell runtime.heap location
              { cell with rc := 0, persistent := true } with
          | none =>
              rw [replacedEq] at semanticUpdate
              contradiction
          | some parentHeap =>
              rw [replacedEq] at semanticUpdate
              have parentRuntimeEq := Except.ok.inj semanticUpdate
              subst parentRuntime
              obtain ⟨result, concreteFold, filteredRelated⟩ :=
                ownershipRelated.foldlM_markPersistent_refines parentRelated recurse
              have foldEq := objectRelated.foldl_markPersistent_closureOwnedValues fuel
                ({ runtime with heap := parentHeap } : RuntimeState)
              rw [← foldEq] at filteredRelated
              have rootHeapEq :
                  markPersistentLocationFuel (fuel + 1) runtime.heap location =
                    captures.toList.foldl (init := parentHeap)
                      (fun heap value =>
                        match value with
                        | .object (.heap child) =>
                            markPersistentLocationFuel fuel heap child
                        | _ => heap) := by
                simp only [markPersistentLocationFuel, found]
                rw [if_neg (by simp [live, ordinary])]
                rw [replacedEq, objectEq]
                simp only [HeapObject.ownedValues]
                rw [← Array.foldl_toList]
                rfl
              have addressHeap :=
                (MemoryState.PrefixExtension.readLiveHeader_facts state address header
                  headerRead).1
              have headerOrdinary : header.persistent = false :=
                persistent.trans ordinary
              have concreteOperation :
                  markPersistentFuel (fuel + 1) state address
                    witness.closureDescriptors =
                    .ok result := by
                simp only [markPersistentFuel]
                rw [addressHeap, headerRead]
                simp only [liftMemory, Bind.bind, Except.bind]
                rw [if_neg (by simp [headerOrdinary])]
                rw [ownedRead, parentWrite]
                exact concreteFold
              refine ⟨result, concreteOperation, ?_⟩
              rw [foldl_markPersistentValueFuel] at filteredRelated
              simpa [rootHeapEq] using filteredRelated

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
