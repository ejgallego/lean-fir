---
id: FIR-BUG-wasm-none-integer-cellrel-exhaustiveness
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: d662b4e
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-07-23
reproduction: Fir/Wasm/Concrete/BoxingCorrectness.lean
regression: Fir/Wasm/Concrete/ClosureProjectionCorrectness.lean
---

# Summary

Extending `LiveCellRel` with heap integers left three impossible descriptor or
heap-object cases absent from boxing and closure-projection proofs, so clean
Talos builds rejected otherwise valid exhaustive arguments.

## Minimal reproduction

Cleanly elaborate `BoxingCorrectness.lean` after the heap-integer relation
lands. The boxed-scalar decoder must rule out an `.integer` descriptor where
the theorem assumes `.boxed`. Cleanly elaborate
`ClosureProjectionCorrectness.lean`; both closure theorems must rule out an
integer heap object where the semantic object is known to be a closure.

## Exact commands

```text
make talos-setup
make talos-check
```

The failure is also visible by directly elaborating the two reproduction
modules instead of reusing their pre-integer oleans.

## Expected semantics

The existing descriptor and semantic-object equalities make all three integer
branches contradictory. Adding a new live-cell representation must preserve
exhaustiveness of consumers that refine only boxed or closure cells.

## Actual behavior

Stale proof oleans made the aggregate check appear green until a clean build.
Fresh elaboration reported missing `.integer` cases in one boxed-scalar proof
and two closure matching/projection proofs.

## Proof or differential evidence

`LiveHeapRel.readBoxedScalar_heap_refines`,
`LiveHeapRel.closureMatches_refines`, and
`LiveHeapRel.projectClosureCapture_refines` each failed at their case analysis
over the extended live-cell relation.

## Semantic impact

Runtime behavior and the heap-integer layout were unaffected, but clean proof
builds—and therefore downstream generation rebases—were blocked.

## Classification and triage

This is Wasm refinement-proof exhaustiveness debt introduced by the
heap-integer extension, not a source or target semantic mismatch.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

W6.6cb adds the three impossible integer cases using the existing exact
descriptor or heap-object equalities. Forced direct elaboration of both
modules and a clean `make talos-setup && make talos-check` are the permanent
regression gates.
