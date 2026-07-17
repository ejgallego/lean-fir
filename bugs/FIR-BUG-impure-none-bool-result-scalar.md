---
id: FIR-BUG-impure-none-bool-result-scalar
status: fixed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: impure
pass: none
discovered-by: differential-test
first-seen: 2026-07-17
reproduction: Fir/Validation/Corpus.lean#nat-list-nonempty-bool
regression: Fir/Validation/Corpus.lean#nat-list-nonempty-bool
---

# Summary

The validation decoder rejects a compiler-produced scalar `UInt8` Boolean
result even though native Lean returns the corresponding `Bool` value.

## Minimal reproduction

Compile a function that pattern matches on a nonempty `List Nat` and returns
`true` from the selected arm. Lean 4.32's final impure LCNF returns
`ScalarValue.uint8 1` for the Boolean result.

## Exact commands

From a clean checkout containing the `nat-list-nonempty-bool` corpus fixture:

```sh
python3 scripts/validate_interpreters.py \
  --case nat-list-nonempty-bool \
  --plan validation-plans/native-lcnf.json
```

## Expected semantics

Native Lean returns `true`. The LCNF observation decoder should interpret the
compiler's scalar `UInt8` value `1` as the same protocol Boolean.

## Actual behavior

LCNF execution reaches `return` with `ScalarValue.uint8 1`, then the validation
adapter fails with `cannot decode ... ScalarValue.uint8 1 as ... bool`.

## Proof or differential evidence

The retained LCNF diagnostics report `cases,lit,return` and five successful
interpreter steps before observation decoding fails. The native backend emits
the protocol datum `{ "bool": { "value": true } }` for the same case.

## Semantic impact

Compiler-generated functions returning unboxed `Bool` values cannot be used as
validation or Wasm-oracle fixtures, even when their LCNF execution is otherwise
inside the supported fragment.

## Classification and triage

This is currently classified as `fir-semantics`: the validation boundary
encodes Boolean inputs as tagged objects but does not admit the scalar result
representation produced by Lean 4.32. The fix must determine whether both
representations are valid at the schema boundary.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

The LCNF validation decoder now accepts scalar `UInt8` zero and one as the
compiler's unboxed Boolean representation while continuing to reject other
scalar values. The Wasm validation schema admits `Bool` over `uint8`, and the
V8 schema decoder applies the same range check. The
`nat-list-nonempty-bool` case permanently checks native Lean, LCNF, and V8 at
this boundary.
