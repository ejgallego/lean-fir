---
id: FIR-BUG-impure-none-decLocation-opaque-proof-boundary
status: candidate
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: impure
pass: none
discovered-by: proof
first-seen: 2026-07-18
reproduction: Fir/LeanIR/Runtime.lean
regression: none
---

# Summary

The recursive semantic `decLocation` operation is an opaque `partial def`, so
Lean exposes no defining equation with which to prove reference-count and
recursive-release refinements.

## Minimal reproduction

Assume a live, nonpersistent heap cell with reference count greater than one
and try to reduce `decValueOnce runtime (.object (.heap location)) check` to
the expected `setCell` update. Reduction stops at `decLocation runtime
location` even though the successful branch is nonrecursive.

## Exact commands

Run `lean-beam update Fir/Wasm/Concrete/ReferenceCountCorrectness.lean` and
attempt `unfold Fir.LeanIR.Impure.decLocation` in the above-one semantic proof.

## Expected semantics

The executable semantic runtime should expose a theorem-grade equation for
each decrement branch, including the recursive zero transition, so the W6
concrete operation can refine it structurally.

## Actual behavior

Lean prints `decLocation` as `opaque`; `unfold` fails and there is no generated
`decLocation.eq_1` or `decLocation.eq_def` declaration.

## Proof or differential evidence

The concrete boxed decrement theorem reaches the exact header count
`cell.rc - 1`, but the corresponding semantic goal cannot inspect the
definition beyond `decLocation runtime location`.

## Semantic impact

Execution and differential tests still run, but W6 cannot prove above-one
decrement, zero-transition deletion, recursive child release, reset, or reuse
against the source runtime definition.

## Classification and triage

This is a proof interface defect in the shared impure runtime rather than a
known execution mismatch. The safe fix is a standalone shared-contract commit
that replaces opaque recursion with an explicit fuel-indexed total definition
and a public wrapper, followed by rebasing both feature branches.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

unresolved
