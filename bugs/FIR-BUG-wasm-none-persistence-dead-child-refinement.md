---
id: FIR-BUG-wasm-none-persistence-dead-child-refinement
status: confirmed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 66cc217
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-07-21
reproduction: Fir/Wasm/Concrete/PersistenceCorrectness.lean
regression: none
---

# Summary

`LiveHeapRel` permits a live constructor or closure to own a mapped semantic
heap reference whose target cell is already dead. FIR cache persistence skips
that dead child and succeeds, while concrete recursive persistence attempts
`readLiveHeader` on its freed allocation and returns a target fault.

## Minimal reproduction

Construct a related heap with a live parent object field mapped to a canonical
`DeadCellRel` child. Run `RuntimeState.markPersistent` on the parent and
`markPersistentFuel` on its concrete address. The semantic child step observes
`cell.live = false` and is an exact no-op; the concrete child step rejects the
freed header before it can return unchanged.

## Exact commands

Inspect the child-recursion obligation after
`LiveHeapRel.markPersistentFuel_refines_constructor_step` in
`Fir/Wasm/Concrete/PersistenceCorrectness.lean` and attempt to close the global
fuel induction from `LiveHeapRel` alone.

## Expected semantics

Either the heap refinement must state the semantic ownership invariant that
every heap reference reachable through a live object's owned values points to
a live cell, or concrete persistence must deliberately mirror FIR's dead-cell
no-op. The chosen contract must make recursive cache publication total on all
states admitted by the refinement.

## Actual behavior

`ValueRel` proves only that an owned heap location maps to a concrete address.
`LiveHeapRel.concreteToSemantic` may return `CellRel.dead` for that address, so
the current relation supplies no liveness fact to recursive persistence.

## Proof or differential evidence

The metadata rewrite, boxed/natural leaf theorem, ordered ownership fold, and
constructor/closure recursive-step theorems all compose. The remaining child
induction cannot prove the concrete zero/dead branch from the semantic no-op
without an additional reachability-liveness invariant.

## Semantic impact

Constructive `CachePersistenceRefines` for arbitrary mapped constructor and
closure graphs cannot be derived from `ConcreteRuntimeRel` and `ValueRel` as
currently defined. Executable well-formed programs are expected to maintain
live ownership, but that invariant is absent from the proof boundary.

## Classification and triage

This is a refinement-model/adapter contract defect exposed by proof. No
workaround should weaken ordinary object decoding or silently assume child
liveness at each recursive call.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Open. Prefer a reusable owned-reference liveness invariant preserved by
allocation, mutation, reset/reuse, release, and persistence; then consume it
once in the global persistence induction.
