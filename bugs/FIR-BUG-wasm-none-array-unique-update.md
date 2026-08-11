---
id: FIR-BUG-wasm-none-array-unique-update
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: resident-runtime-test
first-seen: 2026-08-12
reproduction: integration/talos/artifact/run-resident-arrays.mjs
regression: integration/talos/artifact/resident-array-client.mjs
---

# Summary

The resident `Array` helper allocates every value as persistent with reference
count zero, ignores the requested capacity of `Array.emptyWithCapacity`, and
allocates a fresh exact-size array for every `push`, `uset`, and nonempty
`pop`. This loses Lean's exclusive-update and amortized-growth semantics.

## Minimal reproduction

Create `Array.emptyWithCapacity 4`, record the heap frontier, and push one
element. The fresh array must be live with reference count one, capacity four,
and the push must return the same address without moving the frontier.

## Exact commands

```sh
cd integration/talos/artifact
lake exe fir-wasm-artifact resident-arrays _build/resident-arrays.wasm
node run-resident-arrays.mjs _build/resident-arrays.wasm
```

## Expected semantics

Lean's generic runtime allocates ordinary reference-counted arrays. `push`
updates an exclusive array in place while capacity remains, `uset` and `pop`
update an exclusive array in place, and shared or persistent inputs take a
copy-on-write path that consumes one ordinary input reference. Capacity grows
according to the runtime's `(capacity + 1) * 2` rule.

## Actual behavior

The resident header is always live-persistent with reference count zero and
capacity equal to size. `emptyWithCapacity` returns capacity zero regardless
of its argument. Each mutating operation allocates and copies unconditionally,
including updates for which the input is demonstrably exclusive.

## Proof or differential evidence

The real-engine resident Array fixture asserts header ownership, requested
capacity, address identity, and frontier stability. Before repair it fails on
the first fresh-array ownership assertion because the helper writes persistent
flags instead of ordinary live flags.

## Semantic impact

The value-level array contents remain plausible, but compiled builders become
quadratic and retain dead copies in the instance arena. More importantly, the
generated runtime no longer implements Lean's ownership contract, so programs
that rely on uniqueness for practical execution can become unusable in Wasm.

## Classification and triage

This is a resident-runtime compiler defect. Lean's LCNF calls the ordinary
Array runtime API; the discrepancy is introduced by FIR's persistent-arena
Array implementation.

## Workaround

None. Replacing arrays with host-side JavaScript buffers or application-specific
facades would bypass the compiled Lean semantics.

## Upstream tracking

none

## Resolution and regression

The resident Array layout now distinguishes persistent boundary graphs from
ordinary live arrays. Fresh arrays start at reference count one and retain
their requested capacity; `push`, `uset`, and `pop` reuse exclusive arrays,
while shared and persistent arrays take copy-on-write paths. Growth follows
Lean's `(capacity + 1) * 2` rule.

Element ownership is part of the repair rather than an address-only
optimization: owned reads retain their result, copies retain every copied
child, replacements and pops release removed children, `replicate` accounts
for each stored reference, and final Array release recursively releases the
live prefix. The real-engine fixture covers immediate and allocated children,
exclusive/shared/persistent paths, consumed input references, final recursive
release, and zero-length `replicate` consumption.
