---
id: FIR-BUG-impure-none-bool-entry-scalar-abi
status: fixed
classification: validation-harness
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: impure
pass: none
discovered-by: differential-test
first-seen: 2026-07-31
reproduction: Fir/Validation/Corpus.lean#capturedBoolPartial
regression: Fir/Validation/Corpus.lean#capturedBoolPartial
---

# Summary

The validation adapter encodes runner-supplied `Bool` arguments as tagged
objects, but Lean's final impure LCNF entry ABI represents `Bool` as an unboxed
`UInt8` scalar. Capturing such an argument in a partial application therefore
faults at the compiler-generated `box` instruction before the source program
runs.

## Minimal reproduction

Pass either Boolean value to `capturedBoolPartial`. The source entry partially
applies `selectCapturedBool` to the argument and invokes the resulting closure.
Final LCNF boxes the captured Boolean before storing it in the closure.

## Exact commands

From this candidate fixture checkout:

```sh
python3 scripts/validate_interpreters.py \
  --plan validation-plans/native-lcnf.json \
  --case captured-bool-partial-true \
  --case captured-bool-partial-false \
  --out-dir _build/validation-bool-scalar-before
```

## Expected semantics

Native Lean returns `1` for `true` and `0` for `false`. The candidate receives
the same scalar ABI values, boxes them for closure storage, unboxes them in the
callee, and returns the same results.

## Actual behavior

Native Lean returns the expected Naturals. The LCNF interpreter executes
`admin:invoke-name` followed by `form:box`, then terminates both cases with:

```text
Fir.LeanIR.Impure.RuntimeFault.expectedScalar
```

## Proof or differential evidence

Validation run
`fcd103e5fdf020e697e49d2450a4088d46e3c595f413849cef04f18772ddfde5`
retains immutable evidence
`9b30f4e9e20272d6ca313d4a0bef3989514f4e79116e5c8db9fa497a0f2e6fb1`
and matrix
`a8c8fd69a8a225cbe911963280c2d8bdcf6bf91b20dd1818514da0d49bc3c60c`.
Both comparisons are unequal. Static coverage contains `box`, `pap`, `fap`,
`cases`, `lit`, and `return`; executed coverage stops after exactly two
interpreter steps at the first `box`.

## Semantic impact

Any validation fixture whose compiler-generated entry captures a
runner-supplied Boolean can report an interpreter semantic failure before
reaching the intended operation. Direct branch fixtures can mask the malformed
entry representation because they do not necessarily force scalar boxing.

## Classification and triage

The candidate has been minimized to the validation boundary. The
compiler-generated `box` correctly requires a scalar and native Lean confirms
the source result, while the adapter constructs `.object (.tagged 0|1)`.
Classification is therefore `validation-harness`, not compiler, interpreter,
W6 runtime, or W7 generation.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

`encodeDatum` now supplies `.scalar (.uint8 0|1)` for Boolean entry arguments,
matching Lean's final impure LCNF ABI. A local guard pins both encodings without
allocating heap state. The two native-oracle regressions cover both values and
require the exact 15-form execution trace, including one `box`, one `pap`, one
`unbox`, three calls, and the scalar branch.

Post-repair run
`828be352c140bdc0206db85be478281e9a32bdfdcd079d1015704ab08b3e4f4e`
retains evidence
`001823a9a77bb9c78278f40397533661b47de260f2cb4d27f81392c0a23dfba7`
and matrix
`1e33217abbd0ce2c447cef38dc95d2fcd77064bb8c78a0bd42bc305353a15a98`.
Both comparisons are equal with zero findings.
