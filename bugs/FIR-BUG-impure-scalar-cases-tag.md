---
id: FIR-BUG-impure-scalar-cases-tag
status: fixed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: impure
pass: none
discovered-by: differential-test
first-seen: 2026-07-16
reproduction: Fir/Validation/Corpus.lean#scalar-enum-cases
regression: Fir/LeanIR/InterpreterExamples.lean#scalarCaseProgram
---

# Summary

FIR's impure interpreter rejects scalar-encoded constructor discriminants,
while Lean's final impure LCNF uses `cases` directly on nullary enums lowered
to fixed-width scalars.

## Minimal reproduction

Define a three-constructor nullary enum, pass its third constructor to a
noinline pattern-matching function, and return a distinct natural from each
branch. Lean lowers the enum literal to `LitValue.uint8` and the callee to
`cases` over that scalar parameter.

## Exact commands

From a clean checkout containing the `scalar-enum-cases` corpus fixture:

```sh
python3 scripts/validate_interpreters.py --case scalar-enum-cases
```

## Expected semantics

Lean's native compiler returns 30 for the third constructor. The LCNF
interpreter should obtain tag 2 from the `UInt8` discriminant, select the same
constructor alternative, and return 30.

## Actual behavior

The interpreter executes `fap`, `lit`, and `cases`, then terminates with
`RuntimeFault.expectedConstructor` instead of returning 30.

## Proof or differential evidence

The generated final impure artifact has no externals and contains `let choice
: UInt8 := 2; ... cases choice`. `Runtime.getTag` accepts tagged and heap object
values only, so it rejects `.scalar (.uint8 2)` before branch selection.

## Semantic impact

Pattern matching on compiler-unboxed nullary enumerations is outside FIR's
current executable semantics. This affects ordinary source programs and
closure bodies, not malformed hand-written LCNF.

## Classification and triage

This is classified as `fir-semantics`: the compiler artifact is well-typed and
executes natively, while FIR's generic `cases` implementation omits scalar
discriminants.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

`Runtime.getTag` now interprets fixed-width scalar and `USize` values as
constructor tags in addition to object values. `scalarCaseProgram` directly
checks the interpreter boundary, while the `scalar-enum-cases` differential
fixture permanently checks Lean's compiler-generated representation against
native execution.
