---
id: FIR-BUG-wasm-none-partial-apply-tagged-result
status: candidate
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-07-20
reproduction: Fir/Wasm/ABI.lean
regression: none
---

# Summary

The semantic Wasm ABI accepts `.tagged` as the result kind of `partialApply`,
although every partial application allocates and returns a heap closure.

## Minimal reproduction

Construct `.partialApply function 2 1 #[.tobject] .tagged` and evaluate
`RuntimeOp.abiWellFormed`. The check succeeds because `.tagged.isObjectLike`
is true.

## Exact commands

Run `lake build Fir.Wasm.Examples`, then inspect the `partialApply` branch of
`RuntimeOp.abiWellFormed` in `Fir/Wasm/ABI.lean`. Its only result constraint is
`result.isObjectLike`.

## Expected semantics

A successful partial application returns `.object (.heap location)`. Its
concrete address can refine `.object` or widen to `.tobject`, but cannot refine
the exact `.tagged` ABI kind.

## Actual behavior

The validator admits `.tagged`, so a structurally accepted runtime import may
request a result relation that no closure allocation can inhabit.

## Proof or differential evidence

`allocateClosure_liveHeapRel` proves exact `.object` and `.tobject` results.
The W6.6 composition obligation for the admitted `.tagged` case is impossible:
`ValueRel .tagged` requires a semantic tagged reference, while the source
interpreter returns a fresh heap reference.

## Semantic impact

A full correctness theorem cannot cover every operation accepted by
`RuntimeOp.abiWellFormed`; the concrete `partialApply` slice must temporarily
exclude the `.tagged` result case.

## Classification and triage

This appears local to the Wasm adapter's validation predicate. Compiler-
produced partial applications are expected to use `object` or `tobject`, but
that claim still needs a captured-artifact audit before narrowing the ABI.

## Workaround

The W6.6 refinement is restricted to `.object` and `.tobject` results without
changing or weakening `ValueRel`.

## Upstream tracking

none

## Resolution and regression

unresolved
