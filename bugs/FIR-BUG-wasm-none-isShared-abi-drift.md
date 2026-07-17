---
id: FIR-BUG-wasm-none-isShared-abi-drift
status: fixed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-07-16
reproduction: Fir/Wasm/Examples.lean#rcProgram
regression: Fir/LeanIR/InterpreterExamples.lean#isSharedCaseProgram
---

# Summary

FIR's repaired `isShared` interpreter result is a tagged object, while Lean
4.32 final impure LCNF and FIR's frozen semantic-Wasm ABI type the operation as
`UInt8`.

## Minimal reproduction

Lower `rcProgram` after the interpreter fixture binds its `isShared` result as
`LCNF.ImpureType.object`. `Fir.Wasm.lower` rejects the program because the
runtime import is specified to return `AbiKind.uint8`.

## Exact commands

From the repository root:

```sh
lake build Fir.Wasm.Examples
```

The `lowers? rcProgram` and `lowers? persistentRcProgram` guards fail with
`CompileError.malformed "isShared must produce UInt8"`.

## Expected semantics

The FIR interpreter and semantic-Wasm ABI should agree with the pinned Lean
compiler on one representation. Lean 4.32's `ExpandResetReuse` creates the
`isSharedCheck` binding and its join-point parameter with impure type `uint8`,
and scalar case discriminants are valid final impure LCNF.

## Actual behavior

`Runtime.isShared` now returns `.object (.tagged 0)` or `.object (.tagged 1)`,
and the hand-written interpreter fixtures declare an `object` result. The
Wasm ABI still declares `.isShared` as `tobject -> uint8`, so its lowerer
correctly rejects those changed fixtures.

## Proof or differential evidence

Lean 4.32's `Lean.Compiler.LCNF.ExpandResetReuse` constructs both the
`isShared` let declaration and the corresponding join-point parameter with
`uint8`. FIR's scalar-case semantics can now branch on that representation,
so changing only `Runtime.isShared` and hand-written result types creates an
inconsistent semantic boundary rather than matching the compiler artifact.

## Semantic impact

The inconsistency breaks the Wasm lowering regression corpus immediately. It
also prevents a sound W5 ownership contract: a host returning a tagged object
cannot satisfy the existing `uint8` import signature, while changing the
signature would reject compiler-generated final impure LCNF.

## Classification and triage

This is classified as `fir-semantics` because the pinned Lean compiler's final
impure type and the local executable runtime disagree. The Wasm lowerer is the
first static consumer to reject the drift.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

FIR's shared runtime now returns `.scalar (.uint8 0)` or
`.scalar (.uint8 1)`, and the hand-written `rcProgram`,
`persistentRcProgram`, and `isSharedCaseProgram` declarations use the same
`UInt8` type emitted by Lean 4.32. `Fir/Wasm/Examples.lean` permanently checks
that the repaired programs lower against the frozen semantic ABI.
