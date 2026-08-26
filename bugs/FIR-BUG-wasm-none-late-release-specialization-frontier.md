---
id: FIR-BUG-wasm-none-late-release-specialization-frontier
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-08-26
reproduction: Fir/Wasm/Emit/ScalarBoxingExamples.lean
regression: Fir/Wasm/Emit/ScalarBoxingExamples.lean
---

# Summary

Persistent resident planning can specialize a checked decrement after the
release-helper inventory has been fixed, leaving the newly selected unchecked
decrement on the unresolved runtime frontier.

## Minimal reproduction

Compile and resident-link the non-generation-ready Float32 scalar-boxing
fixture. Its exact boxed wrapper owns a definite heap object, so release
specialization changes its checked decrement to the unchecked form. The input
module contains no other unchecked decrement.

## Exact commands

From the repository root:

```sh
bash integration/talos/artifact/check.sh
```

## Expected semantics

Release operand specialization must happen before the persistent linker
inventories runtime operations and builds release helpers. The linked Float32
fixture should retain exactly its deliberately unsupported box and unbox
operations.

## Actual behavior

The persistent plan inventories and internalizes the checked decrement first,
then specializes the real source body to an unchecked decrement while
materializing the plan. Since no unchecked decrement was present in the
planning view, no rewrite or helper exists for it and the operation remains on
the linked frontier.

## Proof or differential evidence

`ScalarBoxingExamples.lean` rejects the linked Float32 frontier containing
`box Float32`, `dec 1 false`, and `unbox Float32`; before release specialization
the fixture contains only the checked decrement and the intended box/unbox
frontier.

## Semantic impact

A module whose exact object release is the first occurrence of an unchecked
decrement can fail an otherwise complete resident link or retain an unexpected
function import. Modules already containing the unchecked operation conceal
the ordering defect because the persistent plan happens to build the required
helper.

## Classification and triage

This is a resident-linker planning-order defect. The ownership classification
and checked-to-unchecked specialization are sound, but the specialized
operation is introduced too late for helper discovery.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

`ResidentRelease.specializeCheckedDecrements` now specializes every source
function and immediately rebuilds the module's runtime-operation and import
inventories. `ResidentLinker.linkModule` applies that normalization after
call-result refinement but before persistent planning, so the releases step
discovers and internalizes every selected decrement form. The Float32 scalar
boxing frontier is the regression: its only unchecked decrement is created by
this normalization, and the linked fixture must retain only its reviewed
unsupported box/unbox pair.
