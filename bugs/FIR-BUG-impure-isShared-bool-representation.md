---
id: FIR-BUG-impure-isShared-bool-representation
status: fixed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: impure
pass: none
discovered-by: differential-test
first-seen: 2026-07-16
reproduction: Fir/Validation/Corpus.lean#packed-preserve
regression: Fir/LeanIR/InterpreterExamples.lean#isSharedCaseProgram
---

# Summary

FIR's impure interpreter originally represented `isShared` as scalar `UInt8`,
but its case discriminator path originally accepted only object constructors.

## Minimal reproduction

Compile a function that allocates a constructor and returns an updated copy.
Lean's reset/reuse lowering emits `isShared object` followed by `cases` on its
result. Both `packed-preserve` and `tuple-rotate` in the native-validation
corpus reach this sequence.

## Exact commands

From a clean checkout:

```sh
python3 scripts/validate_interpreters.py --case packed-preserve
python3 scripts/validate_interpreters.py --case tuple-rotate
```

## Expected semantics

The LCNF interpreter should return the same packed `UInt32` or nested product
as Lean's native compiler. Lean 4.32 gives `isShared` impure result type
`UInt8`; scalar cases interpret `0` and `1` as the `Bool.false` and
`Bool.true` alternative tags.

## Actual behavior

Both LCNF executions terminate with
`RuntimeFault.expectedConstructor` at the `cases` immediately following
`isShared`; native execution returns normally because scalar case
discriminants are valid.

## Proof or differential evidence

The generated artifacts contain `let isSharedCheck := isShared value; cases
isSharedCheck`. Lean's `ExpandResetReuse` constructs that binding and its join
parameter with type `UInt8`. The failing FIR revision routed `cases` through a
`getTag` that accepted only tagged or heap object values.

## Semantic impact

Any final impure LCNF that executes ownership-guided reset/reuse control flow
can fault before reaching the reuse or allocation branch. This removes a large
class of compiler-generated constructor programs from the interpreter's valid
domain.

## Classification and triage

This is classified as `fir-semantics`: the final LCNF artifact is well-typed
and native Lean executes it, while the mismatch is internal to FIR's runtime
value chosen for `isShared`.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

FIR's `getTag` accepts scalar and `USize` discriminants, while `isShared`
retains Lean 4.32's scalar `UInt8` result. The direct `isSharedCaseProgram`
interpreter guard and the compiler-generated `packed-preserve` and
`tuple-rotate` differential cases cover the repaired boundary. A later
temporary change to tagged objects was reverted under
`FIR-BUG-wasm-none-isShared-abi-drift`.
