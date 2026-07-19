import Fir.Wasm.Concrete.OwnershipFrameCorrectness
import Fir.Wasm.Concrete.ScalarMutationCorrectness

namespace Fir.Wasm.Concrete

open Lean.Compiler
open Fir.LeanIR.Impure

/-- Exact common-header transaction behind a successful concrete constructor
tag update. Exposing the write lets the generic whole-heap frame theorem carry
every non-target allocation. -/
theorem writeTag_header
    {state : MemoryState} {address : Word32} {header : Header}
    (valid : state.FrontierInvariant)
    (headerRead : state.readLiveHeader address = .ok header)
    (headerKind : header.kind = .constructor)
    (headerOwned : address.value + headerBytes ≤ state.heapCursor)
    (tag : Nat) (tagFits : tag < UInt32.size) :
    ∃ result updatedHeader memory,
      writeTag state address tag = .ok result ∧
      updatedHeader = { header with aux0 := UInt32.ofNat tag } ∧
      result = { state with memory } ∧
      updatedHeader.write state.memory address = .ok memory ∧
      result.FrontierInvariant ∧
      result.readLiveHeader address = .ok updatedHeader := by
  obtain ⟨heap, _, live, minimum, aligned, extentInMemory⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header headerRead
  have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
    Nat.le_trans headerOwned valid.cursorInBounds
  have constructorHeader : readConstructorHeader state address = .ok header := by
    unfold readConstructorHeader
    simp [heap, headerRead]
    simp only [Bind.bind, Except.bind]
    simp [liftMemory, headerKind]
    rfl
  let updatedHeader : Header := { header with aux0 := UInt32.ofNat tag }
  obtain ⟨memory, headerWrite, _⟩ :=
    Header.write_spec state.memory address updatedHeader headerInBounds
  let result : MemoryState := { state with memory }
  have operation : writeTag state address tag = .ok result := by
    unfold writeTag
    rw [constructorHeader]
    simp only [Bind.bind, Except.bind]
    rw [uint32Field_eq_ok "constructor tag" tag tagFits]
    change (do
      let memory ← liftMemory (updatedHeader.write state.memory address)
      return ({ state with memory } : MemoryState)) = .ok result
    rw [headerWrite]
    rfl
  have memorySize : memory.size = state.memory.size :=
    Header.write_preserves_size state.memory memory address updatedHeader
      headerInBounds headerWrite
  have decoded : Header.read memory address = .ok updatedHeader :=
    Header.read_of_write_eq_ok state.memory memory address updatedHeader
      headerInBounds headerWrite
  have headerAfter : result.readLiveHeader address = .ok updatedHeader := by
    unfold MemoryState.readLiveHeader
    simp [result, heap, decoded]
    simp only [Bind.bind, Except.bind]
    simp [updatedHeader, live, minimum, aligned, memorySize, extentInMemory]
    rfl
  exact ⟨result, updatedHeader, memory, operation, rfl, rfl, headerWrite,
    valid.writeHeader headerOwned headerWrite, headerAfter⟩

/-- Whole-heap refinement for the successful constructor tag mutation. -/
theorem LiveHeapRel.writeTag_refines
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    {semantic : ConstructorObject}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (tag : Nat) (tagFits : tag < UInt32.size) :
    ∃ result nextRuntime,
      writeTag state address tag = .ok result ∧
      Fir.LeanIR.Impure.setTag runtime (.object (.heap location)) tag =
        .ok nextRuntime ∧
      LiveHeapRel result witness nextRuntime := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  let replacement : HeapCell := {
    cell with object := .ctor { semantic with tag := tag } }
  cases targetRelated with
  | constructor descriptor storedObjectEq objectRelated headerRead headerKind
      refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      have semanticEq := HeapObject.ctor.inj storedObjectEq
      subst semantic
      obtain ⟨result, updatedHeader, memory, operation, updatedEq, resultEq,
          headerWrite, finalValid, headerAfter⟩ :=
        writeTag_header related.frontier headerRead headerKind
          objectRelated.headerOwned tag tagFits
      obtain ⟨localResult, localOperation, objectAfter⟩ :=
        objectRelated.writeTag tag tagFits
      rw [operation] at localOperation
      have resultMatch := Except.ok.inj localOperation
      subst localResult
      have targetAfter : CellRel result witness address replacement := by
        apply CellRel.live
        apply LiveCellRel.constructor descriptor (by rfl) objectAfter headerAfter
        · simpa [updatedEq] using headerKind
        · simpa [replacement, updatedEq] using refCount
        · simpa [replacement, updatedEq] using persistent
        · simpa [replacement] using cellLive
      have oldRawRead :=
        (MemoryState.PrefixExtension.readLiveHeader_facts state address _
          headerRead).2.1
      have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
        Nat.le_trans objectRelated.headerOwned related.frontier.cursorInBounds
      obtain ⟨nextRuntime, semanticSet, heapRelated⟩ :=
        related.setCell_of_headerWrite mapped found descriptor oldRawRead resultEq
          headerInBounds headerWrite (by simp [updatedEq]) finalValid targetAfter
      have sourceOperation :
          Fir.LeanIR.Impure.setTag runtime (.object (.heap location)) tag =
            .ok nextRuntime := by
        simp [Fir.LeanIR.Impure.setTag, modifyConstructor, getConstructor,
          getLiveCell, Bind.bind, Except.bind, found, live, objectEq]
        change setCell runtime location replacement = .ok nextRuntime
        exact semanticSet
      exact ⟨result, nextRuntime, operation, sourceOperation, heapRelated⟩
  | boxed descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | natural descriptor storedObjectEq headerRead headerKind ordinary marker extent
      limbsFit decoded refCount persistent cellLive =>
      rw [objectEq] at storedObjectEq
      contradiction
  | closure closureRelated =>
      obtain ⟨function, arity, captures, storedObjectEq⟩ := closureRelated.objectEq
      rw [objectEq] at storedObjectEq
      contradiction

end Fir.Wasm.Concrete
