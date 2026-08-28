---
id: FIR-BUG-wasm-none-array-exclusive-release-order
status: confirmed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-08-28
reproduction: Fir/Wasm/Emit/ResidentArray.lean
regression: none
---

# Summary

The trusted resident Array exclusive-replacement branch stores the new element
before decrementing the displaced element, reversing Lean 4.33 and FIR's
source-semantic ownership order.

## Minimal reproduction

Inspect `replaceExclusiveElementBody` in `Fir/Wasm/Emit/ResidentArray.lean`:
it loads the old word, stores `valueParam`, and only then executes
`ResidentRelease.checkedDecrementLocal elementLocal`.

Lean 4.33's `lean_array_uset` obtains the exclusive Array, decrements `*it`,
and then assigns `*it = v`.  FIR's `replaceArrayAtExternal` likewise executes
`decValueOnce runtime old true` before `setCell` installs the replacement.

## Exact commands

```text
sed -n '1185,1205p' Fir/Wasm/Emit/ResidentArray.lean
sed -n '1300,1335p' Fir/Validation/LCNF.lean
sed -n '935,950p' .deps/lcnf-c-wasm/lean4/src/include/lean/lean.h
```

## Expected semantics

On the exclusive path, borrow the old slot word, decrement that owned value
exactly once, and then store the consumed replacement.  This is the order in
Lean 4.33's native runtime and in FIR's source external semantics.

## Actual behavior

The resident helper borrows the old word, stores the replacement, and then
decrements the old word.

## Proof or differential evidence

The exact resident load/store proof reaches the old-value release boundary,
but `ResidentOwnershipStep` requires a `LiveHeapRel` before the decrement.  The
physical pre-decrement heap already contains the replacement while the source
runtime still contains the old element.  Re-establishing `LiveHeapRel` first
would instead impose set-then-decrement semantics, contrary to
`replaceArrayAtExternal`.

Commuting the operations would require a new global reference-count-balance or
anti-alias invariant strong enough to exclude an exclusive Array containing
itself.  The accepted W6 relation intentionally does not assume such an
unstated invariant.

## Semantic impact

The discrepancy blocks the installed trusted `Array.uset`, `Array.set`, and
`Array.set!` refinement.  The two orders agree on ordinary balanced exclusive
heaps, but can differ on cyclic or reference-count-inconsistent states admitted
by the current relation, so the proof must not silently commute them.

## Classification and triage

This is a resident helper ordering mismatch, not a layout or Talos execution
issue.  Moving the checked decrement before the store matches Lean's runtime,
matches FIR semantics, and makes the existing ownership-step abstraction
compose without strengthening the shared heap relation.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

unresolved
