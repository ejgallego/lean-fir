import FirTalos.ConcreteArrayPublication

/-! Construction-local region closure survives metadata updates, including
nested cache publication. These facts preserve owned edges, not ordinaryness:
published cells may become persistent. No global admission policy is changed. -/

namespace FirTalos.Concrete

open Lean Fir.LeanIR.Impure Fir.Wasm.Concrete

/-- Reuse the ownership graph frame independently of reference counts,
liveness and persistence metadata. -/
theorem HeapRegionClosed.ofOwnershipFrame
    {cutoff : Location} {before after : Heap}
    (closed : HeapRegionClosed cutoff before)
    (frame : Fir.LeanIR.Passes.ElimDead.HeapOwnershipFrame before after) :
    HeapRegionClosed cutoff after := by
  intro parent cell child above found member
  have same := frame parent
  rw [found] at same
  cases oldFound : findCell? before parent with
  | none => simp [oldFound] at same
  | some old =>
    simp only [oldFound, Option.map_some, Option.some.injEq] at same
    exact closed parent old child above oldFound (by simpa [same] using member)

/-- Recursive persistence preserves every allocation region, including regions
belonging to older suspended initializers. The published root need not lie in
the region; only the separate caller-restoration theorem needs that bound. -/
theorem HeapRegionClosed.markPersistent
    {cutoff : Location} {runtime : RuntimeState}
    (closed : HeapRegionClosed cutoff runtime.heap) (value : Value) :
    HeapRegionClosed cutoff (runtime.markPersistent value).heap := by
  cases value with
  | object reference =>
    cases reference with
    | tagged payload => exact closed
    | heap location =>
      exact closed.ofOwnershipFrame
        (Fir.LeanIR.Passes.ElimDead.heapOwnershipFrame_markPersistentLocationFuel
          (runtime.heap.length + 1) runtime.heap location)
  | usize | scalar | erased | reuseToken => exact closed

theorem HeapRegionClosed.setGlobal
    {cutoff : Location} {runtime : RuntimeState}
    (closed : HeapRegionClosed cutoff runtime.heap) (name : Name) (value : Value) :
    HeapRegionClosed cutoff (runtime.setGlobal name value).heap :=
  closed.markPersistent value

/-- Appending a tagged value to the fresh Array preserves the region established
at allocation. This uses the actual in-place cell replacement, not a fresh
allocation of the final Array or a post-state graph-separation premise. -/
theorem HeapRegionClosed.pushFreshTagged
    {cutoff : Location} {entry : RuntimeState} {capacity : Nat} {payload : UInt64}
    (closed : HeapRegionClosed cutoff (semanticArrayResult entry #[] capacity).heap) :
    HeapRegionClosed cutoff
      (semanticArrayResult entry #[.object (.tagged payload)] capacity).heap := by
  apply closed.pushArray
    (location := entry.nextLocation)
    (cell := semanticArrayCell #[] capacity) (elements := #[]) (capacity := capacity)
    (value := .object (.tagged payload))
    (by simp [semanticArrayResult, findCell?]) rfl
    (by simp [Fir.LeanIR.Impure.setCell, replaceCell, semanticArrayResult, semanticArrayCell])
  intro _ child impossible
  cases impossible

end FirTalos.Concrete
