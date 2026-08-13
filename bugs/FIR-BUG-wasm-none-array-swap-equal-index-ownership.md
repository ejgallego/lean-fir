---
id: FIR-BUG-wasm-none-array-swap-equal-index-ownership
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-08-13
reproduction: integration/talos/artifact/resident-array-client.mjs
regression: integration/talos/artifact/resident-array-client.mjs
---

# Summary

The resident `Array.swap` helper returns its input immediately when both
indices are equal, bypassing Lean's ordinary exclusive-update discipline.

## Minimal reproduction

Create a three-element resident Array with reference count two, then invoke
`Array.swap array 1 1`. FIR returns the shared input address unchanged.

## Exact commands

```sh
cd integration/talos/artifact
lake exe fir-wasm-artifact resident-arrays _build/resident-arrays.wasm
node run-resident-arrays.mjs _build/resident-arrays.wasm
```

## Expected semantics

Upstream `lean_array_fswap` always calls `lean_array_uswap`, which first calls
`lean_ensure_exclusive_array`. Even when both indices are equal, a shared input
must consume one reference and return a distinct exclusive copy.

## Actual behavior

FIR tests index equality before selecting the exclusive or copy-on-write path
and returns the original shared Array directly.

## Proof or differential evidence

The upstream implementation in Lean's `include/lean/lean.h` performs
`lean_ensure_exclusive_array(a)` before loading or storing either indexed
element. The focused resident V8 client observes the contrary input identity
and reference count in FIR.

## Semantic impact

Although the immediate Array contents are equal, the returned value remains
shared. A subsequent consuming mutation allocates in FIR where upstream Lean
has already produced a unique Array. This breaks the runtime ownership and
uniqueness behavior required by compiled Lean code.

## Classification and triage

This is a generic resident Array copy-on-write discrepancy. It is independent
of any application adapter or source program.

## Workaround

None. Do not special-case the application or force a copy at the JavaScript
boundary.

## Upstream tracking

none

## Resolution and regression

Removed the equal-index return before `selectExclusive`. Both indices are
still validated before any ownership change, but every valid swap now follows
the same exclusive-update or copy-on-write path as upstream
`lean_array_uswap`.

The resident Array client requires a shared equal-index swap to consume one
input reference, return a distinct exclusive Array, preserve its contents,
and enable the following mutation to reuse that returned address.
