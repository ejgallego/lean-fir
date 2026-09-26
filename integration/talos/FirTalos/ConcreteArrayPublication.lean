import FirTalos.ConcreteLazyPublication

/-!
Source ownership boundary for the existing copied-Array push refinement.
Retaining the copied elements and releasing the old Array change headers,
not owned edges. This module proves the corresponding fresh-region laws;
it does not supply compiler admission or an initializer execution.
-/

namespace FirTalos.Concrete

open Lean Fir.LeanIR.Impure Fir.Wasm.Concrete

/-- Header-only updates inherit every owned edge from the old cell. -/
theorem HeapRegionClosed.setCell_sameObject
    {cutoff location : Location} {before after : RuntimeState}
    {current replacement : HeapCell}
    (closed : HeapRegionClosed cutoff before.heap)
    (found : findCell? before.heap location = some current)
    (operation : Fir.LeanIR.Impure.setCell before location replacement = .ok after)
    (same : replacement.object = current.object) :
    HeapRegionClosed cutoff after.heap := by
  apply closed.setCell found operation
  intro above child member
  exact closed location current child above found (by simpa [same] using member)

/-- Retention changes only a reference count, including the persistent no-op. -/
theorem HeapRegionClosed.incLocation
    {cutoff location amount : Nat} {before after : RuntimeState}
    (closed : HeapRegionClosed cutoff before.heap)
    (operation : incLocation before location amount = .ok after) :
    HeapRegionClosed cutoff after.heap := by
  unfold Fir.LeanIR.Impure.incLocation at operation
  cases read : getLiveCell before location with
  | error fault => simp [read, Bind.bind, Except.bind] at operation
  | ok cell =>
      have found := (Fir.LeanIR.Passes.ElimDead.getLiveCell_spec read).1
      simp only [read, Bind.bind, Except.bind] at operation
      by_cases persistent : cell.persistent = true
      · rw [ite_eq_left persistent] at operation
        cases Except.ok.inj operation
        exact closed
      · rw [ite_eq_right persistent] at operation
        exact closed.setCell_sameObject found operation rfl

theorem HeapRegionClosed.retainOwnedValue
    {cutoff : Location} {before after : RuntimeState} {value : Value}
    (closed : HeapRegionClosed cutoff before.heap)
    (operation : retainOwnedValue before value = .ok after) :
    HeapRegionClosed cutoff after.heap := by
  cases value with
  | object reference =>
      cases reference with
      | heap location => exact closed.incLocation operation
      | tagged payload => cases Except.ok.inj operation; exact closed
  | usize value | scalar value | erased | reuseToken value =>
      cases Except.ok.inj operation
      exact closed

/-- State-threading composition, also used by recursive release. -/
theorem HeapRegionClosed.foldlM
    {α : Type} {cutoff : Location}
    {step : RuntimeState → α → Except RuntimeFault RuntimeState}
    (preserves : ∀ {before after item}, HeapRegionClosed cutoff before.heap →
      step before item = .ok after → HeapRegionClosed cutoff after.heap)
    {items : List α} {before after : RuntimeState}
    (closed : HeapRegionClosed cutoff before.heap)
    (operation : items.foldlM (init := before) step = .ok after) :
    HeapRegionClosed cutoff after.heap := by
  induction items generalizing before with
  | nil => cases Except.ok.inj operation; exact closed
  | cons item items ih =>
      simp only [List.foldlM_cons, Bind.bind, Except.bind] at operation
      cases head : step before item with
      | error failure => rw [head] at operation; contradiction
      | ok middle =>
          rw [head] at operation
          exact ih (preserves closed head) operation

/-- Recursive release never installs an owned edge, even when it kills cells.
The region predicate includes dead cells, so no liveness premise is hidden. -/
theorem HeapRegionClosed.decLocationFuel
    {fuel cutoff location : Nat} {before after : RuntimeState}
    (closed : HeapRegionClosed cutoff before.heap)
    (operation : decLocationFuel fuel before location = .ok after) :
    HeapRegionClosed cutoff after.heap := by
  induction fuel generalizing before after location with
  | zero => simp [Fir.LeanIR.Impure.decLocationFuel] at operation
  | succ fuel ih =>
      simp only [Fir.LeanIR.Impure.decLocationFuel] at operation
      cases read : getLiveCell before location with
      | error fault => simp [read, Bind.bind, Except.bind] at operation
      | ok cell =>
          have found := (Fir.LeanIR.Passes.ElimDead.getLiveCell_spec read).1
          simp only [read, Bind.bind, Except.bind] at operation
          by_cases persistent : cell.persistent = true
          · rw [ite_eq_left persistent] at operation
            cases Except.ok.inj operation
            exact closed
          · rw [ite_eq_right persistent] at operation
            by_cases zero : cell.rc = 0
            · rw [ite_eq_left zero] at operation
              contradiction
            · rw [ite_eq_right zero] at operation
              by_cases shared : cell.rc > 1
              · rw [ite_eq_left shared] at operation
                exact closed.setCell_sameObject found operation rfl
              · rw [ite_eq_right shared] at operation
                cases parentStep : Fir.LeanIR.Impure.setCell before location
                    { cell with rc := 0, live := false } with
                | error fault => rw [parentStep] at operation; contradiction
                | ok parent =>
                    rw [parentStep] at operation
                    have parentClosed := closed.setCell_sameObject found parentStep rfl
                    dsimp only at operation
                    rw [← Array.foldlM_toList] at operation
                    apply HeapRegionClosed.foldlM (closed := parentClosed)
                      (operation := operation)
                    intro childBefore childAfter value childClosed childStep
                    cases value with
                    | object reference =>
                        cases reference with
                        | heap child => exact ih childClosed childStep
                        | tagged payload =>
                            cases Except.ok.inj childStep
                            exact childClosed
                    | usize value | scalar value | erased | reuseToken value =>
                        cases Except.ok.inj childStep
                        exact childClosed

/-- The source transitions exposed by `pushResidentArrayElementCopied_refines`
preserve the publication region. Bounds on the existing copied elements are
derived from the old Array; only the new value needs an immediate edge bound.
Ownership validity and resource safety remain in the concrete refinement's
contracts. No caller-specific disjointness certificate is used here. -/
theorem HeapRegionClosed.copiedArrayPush
    {cutoff location : Location} {before retained after : RuntimeState}
    {cell : HeapCell} {elements : Array Value} {oldCapacity capacity : Nat}
    {value : Value}
    (closed : HeapRegionClosed cutoff before.heap)
    (found : findCell? before.heap location = some cell)
    (objectEq : cell.object = .array elements oldCapacity)
    (sourceAbove : cutoff ≤ location)
    (added : ∀ child, value = .object (.heap child) → cutoff ≤ child)
    (retain : elements.toList.foldlM (init := before)
      Fir.LeanIR.Impure.retainOwnedValue = .ok retained)
    (consume : decValueOnce (semanticArrayResult retained (elements.push value) capacity)
      (.object (.heap location)) true = .ok after) :
    HeapRegionClosed cutoff after.heap ∧ OrdinaryPersistenceTransport before after := by
  have retainedClosed := HeapRegionClosed.foldlM
    (fun h step => h.retainOwnedValue step) closed retain
  have allocatedClosed : HeapRegionClosed cutoff
      (semanticArrayResult retained (elements.push value) capacity).heap := by
    apply retainedClosed.alloc (object := .array (elements.push value) capacity)
      (persistent := false) rfl
    intro child member
    simp only [HeapObject.ownedValues, Array.toList_push, List.mem_append,
      List.mem_singleton] at member
    rcases member with old | new
    · exact closed location cell child sourceAbove found
        (by simpa [objectEq, HeapObject.ownedValues] using old)
    · exact added child new.symm
  refine ⟨allocatedClosed.decLocationFuel consume, ?_⟩
  exact (List.foldlM_ordinaryPersistenceTransport
    (fun step => retainOwnedValue_ordinaryPersistenceTransport step) retain).trans
      ((alloc_ordinaryPersistenceTransport
        (object := .array (elements.push value) capacity) rfl).trans
          (decValueOnce_ordinaryPersistenceTransport consume))

end FirTalos.Concrete
