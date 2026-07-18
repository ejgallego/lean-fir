---
id: FIR-BUG-wasm-none-heap-refinement-release-fuel
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: e64abaf
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-07-18
reproduction: Fir/Wasm/Concrete/HeapRefinement.lean
regression: Fir/Wasm/Concrete/HeapRefinement.lean
---

# Summary

The whole-heap refinement does not connect semantic heap size to the concrete
allocated prefix, so it cannot justify the independent recursive-release fuel
bounds.

## Minimal reproduction

Attempt to compose `decLocationFuel (runtime.heap.length + 1)` with
`decrementReferenceOnceFuel (state.heapCursor / headerBytes + 1)` for related
states. `LiveHeapRel` provides header ownership for every mapped cell but no
cardinality or byte-capacity inequality from which
`runtime.heap.length ≤ state.heapCursor / headerBytes` follows.

## Exact commands

Inspect the `LiveHeapRel` fields in
`Fir/Wasm/Concrete/HeapRefinement.lean`, then attempt the top-level recursive
release refinement in `Fir/Wasm/Concrete/OwnershipFrameCorrectness.lean`.
After the common-fuel induction, the remaining concrete fuel monotonicity step
requires the missing bound.

## Expected semantics

Every semantic heap entry represented by W6 consumes at least one concrete
common header. The semantic heap therefore consumes no more than
`heap.length * headerBytes` bytes of the monotone concrete allocation prefix.
Fresh semantic allocation extends both sides, concrete-only promoted tags only
increase capacity, and ownership updates preserve both sizes.

## Actual behavior

`LiveHeapRel` separately records semantic lookup coverage and concrete
descriptor ownership. It does not retain their aggregate fuel/capacity
consequence, making the concrete and semantic recursive bounds unrelated in
the proof model.

## Proof or differential evidence

The recursive child-list correspondence and same-fuel simulation can be
stated, but lifting the concrete result to its public cursor-derived fuel has
no available premise comparing that fuel with `runtime.heap.length + 1`.

## Semantic impact

This blocks the whole-heap recursive constructor-release theorem. Adding the
inequality only as a theorem argument would make every ownership caller carry
an invariant already established and preserved by allocation.

## Classification and triage

This is a refinement-model defect, not observed runtime divergence. Both fuel
formulas are deliberately conservative; the missing fact is their shared
allocation-capacity invariant.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Resolved in W6.3r by adding `releaseFuelBound` to `LiveHeapRel`:
`semantic.heap.length * headerBytes ≤ state.heapCursor`. Constructor and boxed
allocation establish the extra header capacity, concrete-only promoted-tag
allocation and prefix extension preserve it monotonically, and semantic cell
replacement preserves heap length while header writes preserve the cursor.
`LiveHeapRel.semanticFuel_le_concreteFuel` is the permanent public-fuel
comparison used after the same-fuel recursive simulation.
