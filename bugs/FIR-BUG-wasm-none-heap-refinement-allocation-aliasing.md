---
id: FIR-BUG-wasm-none-heap-refinement-allocation-aliasing
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-07-18
reproduction: Fir/Wasm/Concrete/HeapRefinement.lean
regression: Fir/Wasm/Concrete/HeapRefinement.lean
---

# Summary

The whole-heap refinement records address injectivity but not spatial disjointness of the concrete allocations named by its descriptors.

## Minimal reproduction

Take two distinct semantic locations mapped to distinct concrete words and try to prove that decrementing the first location preserves the second location's decoded `CellRel`. The target operation rewrites 32 header bytes, while `RefinementWitness.WellFormed.locationInjective` proves only that the two starting words differ.

## Exact commands

Run `lean-beam update Fir/Wasm/Concrete/ReferenceCountCorrectness.lean` and attempt to lift `LiveCellRel.decrementReferenceOnce_refines_above_one` to a `LiveHeapRel` postcondition without adding a frame premise.

## Expected semantics

Every address introduced by the concrete allocator denotes a complete, non-overlapping allocation. Rewriting one allocation's header must preserve all decoders rooted at other descriptor addresses.

## Actual behavior

`LiveHeapRel` retains only header ownership and witness address injectivity. Distinct aligned start addresses do not by themselves imply that the 32-byte target header is disjoint from another allocation or its payload.

## Proof or differential evidence

The non-target `semanticToConcrete`, `concreteToSemantic`, and promoted-tag obligations require byte-level framing. The available hypotheses establish `left ≠ right`, but the header frame theorem requires one full interval to end before the other begins.

## Semantic impact

Whole-heap preservation for increment, decrement, leaf release, and recursive constructor release cannot be derived from the current global relation. Adding a frame premise at each ownership theorem would hide rather than establish the allocator invariant.

## Classification and triage

This is currently classified as a Wasm-adapter proof-model defect. The executable allocator advances a monotone cursor by the full aligned allocation size; the missing fact is in `LiveHeapRel`, not in observed runtime behavior.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Resolved in W6.3j by making complete descriptor regions and pairwise interval
disjointness part of `LiveHeapRel`. The fresh-descriptor spatial theorem proves
that allocation at the exact old frontier preserves both properties, and the
constructor, boxed-scalar, and promoted-tag allocation refinements now invoke
that theorem. The umbrella concrete proof build checks every allocator and all
dependent operation theorems against the stronger global relation.
