---
id: FIR-BUG-wasm-none-object-nat-fixture
status: confirmed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-07-16
reproduction: Fir/LeanIR/InterpreterExamples.lean
regression: Fir/Wasm/Examples.lean
---

# Summary

Hand-built interpreter fixtures give `Nat` literals the heap-only `object` type even though `Nat` literals have the static impure ABI kind `tobject` and small values evaluate to tagged pointers.

## Minimal reproduction

`literalCode` binds `.lit (.nat 42)` using `objType`, which is `LCNF.ImpureType.object`, and `literalProgram` also declares an `object` result. The interpreter returns `.object (.tagged 42)`.

## Exact commands

Run `lake build Fir.LeanIR.InterpreterExamples Fir.Wasm.Examples` from the repository root. The interpreter guard exposes the tagged result, while the Wasm ABI guards exercise the object-literal compatibility exception.

## Expected semantics

Lean 4.32 defines impure `object` as a heap pointer, `tagged` as a tagged pointer, and `tobject` as their union. A `Nat` literal can produce either representation based on its value, so its static kind should be `tobject`.

## Actual behavior

The manually constructed fixtures use `object` for small `Nat` bindings and returns, but the FIR interpreter correctly evaluates the small literals to tagged object references.

## Proof or differential evidence

Freezing `AbiKind` makes the declaration/literal mismatch visible: `.nat` classifies as `tobject`, while the fixture declaration classifies as `object`.

## Semantic impact

The affected examples are not faithful final-impure snapshots and cannot directly inhabit a theorem domain that assumes Lean's impure type invariants. Compiler-produced final-impure programs are not known to be affected.

## Classification and triage

This is a FIR fixture-model issue, not evidence of a Lean compiler bug. The shared examples should eventually distinguish heap-only objects from possibly-tagged objects.

## Workaround

The symbolic lowerer temporarily accepts `Nat` literals in object-like fixture declarations while preserving the declared semantic kind in locals, results, and imports. The explicit proof-fragment validator does not claim that this repairs the malformed typing invariant.

## Upstream tracking

none

## Resolution and regression

unresolved
