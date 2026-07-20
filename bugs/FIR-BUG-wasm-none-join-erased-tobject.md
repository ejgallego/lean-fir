---
id: FIR-BUG-wasm-none-join-erased-tobject
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-07-18
reproduction: Fir/Validation/Corpus.lean#tupleRotate
regression: Fir/Wasm/Examples.lean
---

# Summary

Lean 4.32's `ExpandResetReuse` deliberately passes the erased sentinel to a
join parameter typed `tobject` on the shared-object path, but FIR's Wasm
lowerer preserves the argument's `erased` lane when assigning that parameter.
The symbolic module validator consequently rejects every generated reset join
with `tobject <- erased`.

## Minimal reproduction

Compile `Fir.Validation.Corpus.Source.tupleRotate` through final impure LCNF,
bypass `WasmSupported`, and validate the result of `Fir.Wasm.lower`. The slow
reset path contains `goto resetjp erased isSharedCheck`; the first `resetjp`
parameter has type `tobject` and is consumed only in the `Bool.false` arm.

## Exact commands

```sh
python3 scripts/validate_interpreters.py \
  --case tuple-rotate \
  --plan validation-plans/native-v8-scalars.json \
  --out-dir /tmp/fir-join-erased-probe
```

## Expected semantics

The source support gate should recognize the compiler's guarded optional-object
join invariant. On the `Bool.true` shared-object path, the erased sentinel may
occupy the physical `i32` join local because every use of that local is
dominated by the companion `Bool.false` case arm. Ordinary join arguments must
continue to refine their declared parameter ABI kinds.

## Actual behavior

Lowering succeeds, but symbolic validation and binary encoding fail with:

```text
stackMismatch ... [AbiKind.tobject] [AbiKind.erased]
```

The same failure occurs in `PackedPoint.setX`, `Assoc.reassoc`, and
`changeOrGrow`.

## Proof or differential evidence

The pinned Lean source constructs the reset join parameter with impure type
`tobject` in `ExpandResetReuse.expand`, while `mkSlowPath` emits
`.jmp resetJpId #[.erased, .fvar isSharedId]`. Native Lean and FIR's LCNF
interpreter execute all five affected corpus cases successfully. A direct
lower/validate probe reproduces the semantic-lane mismatch for each generated
declaration before V8 execution.

## Semantic impact

All compiler-produced constructor update/reuse paths containing expanded reset
joins are excluded from Wasm generation, even though their runtime operations
and physical representation are already implemented.

## Classification and triage

This is a `wasm-adapter` issue. Lean's erased argument is intentional and
guarded by generated control flow; FIR's lowerer and source support predicate
did not retain that control invariant when assigning semantic local kinds.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Fixed. Ordinary typed joins and both guarded reset forms are admitted without
widening `AbiKind.refines`. The erased slow path requires exact
`isShared(object)` provenance, a true-path fact, and false-arm dominance for
every live use. The representation-polymorphic fast path requires the
companion false-path fact, exact provenance for the same `tobject` argument,
and the same dominance check.

Lowering records that second proof with a symbolic `localGetObject` operation.
The validator accepts it only for a `tobject` local; binary encoding and the
Talos adapter erase it to the unchanged physical Wasm `local.get`. The
`mismatchedGuardObjectJoinProgram` regression proves that a guard for one value
cannot refine another. Existing negative fixtures continue to reject unknown
targets, arity and kind mismatches, unguarded erased arguments, and fake guards.

`packed-preserve`, `tuple-rotate`, and `reuse-assoc` pass native-to-V8
differential runs. The two `changeOrGrow` cases were separately resolved by
`FIR-BUG-impure-expandResetReuse-delete-erased` and remain in the default
matrix.
