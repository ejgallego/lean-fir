---
id: FIR-BUG-wasm-none-closure-capture-descriptor-reserved
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-07-18
reproduction: Fir/Wasm/Concrete/Runtime.lean
regression: Fir/Wasm/Concrete/Examples.lean
---

# Summary

Concrete closure allocation reserves `aux3` as zero instead of recording the
static capture-descriptor index required to release object-valued captures.

## Minimal reproduction

Allocate a closure with one object-valued capture, decrement its sole
reference, and try to match the resulting concrete heap with FIR's recursive
release. The header identifies the target and fixed count but carries no way
for the concrete ownership decoder to distinguish the object capture from an
integer or floating-point lane.

## Exact commands

From the Wasm worktree, inspect the frozen layout and the executable decoder:

```sh
sed -n '760,790p' integration/talos/PLAN.md
sed -n '70,120p' Fir/Wasm/Concrete/ClosureRuntime.lean
sed -n '490,515p' Fir/Wasm/Concrete/Runtime.lean
```

The plan assigns `aux3` to a static capture-descriptor index, while allocation
writes zero, metadata validation requires zero, and ownership returns
`unsupportedOwnershipKind .closure`.

## Expected semantics

The concrete closure header must select immutable generated metadata from
which the runtime can recover the ordered `AbiKind` capture descriptor. On a
one-to-zero reference-count transition it must recursively decrement exactly
the object-valued captures, matching `HeapObject.children` in FIR.

## Actual behavior

`allocateClosure` writes zero to `aux3`, `readClosureHeader` rejects every
nonzero value, and `readOwnedReferences` rejects all closure objects. Local
allocation and projection proofs succeed, but the closure cannot enter the
complete heap relation used by ownership correctness.

## Proof or differential evidence

Adding the packaged `ClosureCellRel` case to exhaustive `LiveCellRel` makes
the generic one-to-zero decrement obligation require successful closure
ownership traversal. The only executable branch is the structured target
failure above, and the proof-only capture kinds are intentionally unavailable
to runtime execution.

## Semantic impact

Any concrete closure whose reference count reaches zero fails instead of
releasing its semantic cell and owned object captures. This blocks W6.4
whole-heap closure refinement and would make generated closure-heavy programs
diverge from the semantic Talos oracle.

## Classification and triage

The mismatch is local to the concrete Wasm representation: the W6.0 contract
already reserves the required descriptor index and FIR already exposes the
correct semantic children. The remaining design choice is the deterministic
generated descriptor table and how it is supplied to concrete ownership
operations.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

W6.4h restores the frozen header boundary: allocation resolves the exact
capture descriptor in a deterministic generated table and writes its checked
index to `aux3`; metadata decoding recovers that descriptor, rejects unknown
or wrong-sized entries, and typed projection rejects a same-width kind
reinterpretation. `Fir/Wasm/Concrete/Examples.lean` guards successful index
round-tripping plus both missing-descriptor and wrong-kind failures.

W6.4i completes the executable fix. `readOwnedReferences` resolves `aux3`,
checks descriptor length against the fixed count, filters object-like and
erased lanes in source order, and recursive decrement threads the immutable
table through every child. The permanent `releasedOwnedClosure` regression
allocates a heap constructor plus a scalar capture inside a closure, observes
only the constructor word as owned, and verifies that one-to-zero closure
release marks both parent and child dead.
