---
id: FIR-BUG-wasm-none-liveheaprel-canonical-header-words
status: candidate
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: 0ed547cf114e44a1891c28a650c3b0d9975c12eb
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-08-25
reproduction: integration/talos/FirTalos/ConcreteResidentRelease.lean
regression: integration/talos/FirTalos/ConcreteResidentRelease.lean
---

# Summary

`LiveHeapRel` retains decoded header booleans but does not require canonical
raw header words, so it is not alone strong enough to relate W6's full-header
reference-count rewrite to W7's single-word resident decrement.

## Minimal reproduction

Assume a represented live ordinary cell whose raw flags word has the ordinary
low bit but also an unsupported high bit. `Header.read` decodes the same
`persistent = false` and `live` booleans, so the current `LiveHeapRel` can
admit it. W6's `decrementReferenceOnce` rewrites all eight words using
`Header.words`, thereby canonicalizing flags. W7's `fir_dec_once` hot path
writes only the reference-count word and preserves the noncanonical raw flag.

## Exact commands

From `integration/talos` in the W6 worktree:

```text
lean-beam update FirTalos/ConcreteResidentRelease.lean
lean-beam sync FirTalos/ConcreteResidentRelease.lean
```

Removing the explicit `Header.ExactWords` boundary from
`LiveHeapRel.liveReleaseProgram_aboveOne_refines` leaves the final
`ResidentMemoryRel` obligation unprovable because the two resulting memories
can differ at the flags lane.

## Expected semantics

Every resident allocation admitted by the compiler/runtime simulation should
carry canonical common-header words. Under that invariant, changing only the
logical reference count has exactly the same memory effect as W7's optimized
single `i32.store`.

## Actual behavior

The payload relations generally retain `readLiveHeader`, which is intentionally
lossy for raw flags. Some specialized validator admissions additionally retain
`Header.ExactWords`, but the whole-heap relation does not state a uniform
canonical-header invariant for all mapped live cells.

## Proof or differential evidence

The generic theorem `ResidentMemoryRel.writeHeaderRefCount` requires exact
initial header words in order to cancel the seven same-value W6 stores. The
existing `LiveCellRel.ownershipHeader` provides `Header.read` rather than
`Header.ExactWords`, and canonical flags cannot be derived from that premise.

## Semantic impact

The early shared-reference decrement proof cannot yet be stated from
`LiveHeapRel` and `ResidentMemoryRel` alone. More generally, any resident
helper that preserves raw header lanes while its W6 host counterpart rewrites
canonical decoded headers needs the same invariant.

## Classification and triage

This is currently classified as a Wasm-adapter simulation-relation gap. The
generated allocator is expected to create canonical headers; no executable
counterexample from compiler-generated state is known. The proof must still
record and preserve that fact instead of assuming it implicitly.

## Workaround

The focused decrement theorem temporarily accepts `Header.ExactWords` for the
target allocation as an explicit state invariant. It is not an executable
runtime workaround.

## Upstream tracking

none

## Resolution and regression

Unresolved. The intended resolution is a reusable resident heap relation (or
an equivalent strengthening of the existing simulation boundary) that owns
canonical header words for every mapped live allocation and preserves them
through proved runtime transitions.
