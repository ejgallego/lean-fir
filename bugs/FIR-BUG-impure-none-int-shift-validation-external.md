---
id: FIR-BUG-impure-none-int-shift-validation-external
status: fixed
classification: validation-harness
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: impure
pass: none
discovered-by: differential-test
first-seen: 2026-07-28
reproduction: Fir/Validation/Corpus.lean
regression: Fir/Validation/LCNF.lean
---

# Summary

Source fixtures using `Int.shiftLeft` or `Int.shiftRight` compile to direct final-impure externals that the LCNF validation backend does not model.

## Minimal reproduction

Compile and execute `Source.shiftLeftInt 2147483647 1` or
`Source.shiftRightInt (-340282366920938463463374607431768211473)
340282366920938463463374607431768211473` from the validation corpus.

## Exact commands

Run:

```text
lake --rehash build fir-native-oracle
python3 scripts/validate_interpreters.py \
  --plan validation-plans/native-lcnf.json \
  --tag int-shift-probe \
  --out-dir _build/validation-int-shift-probe
```

## Expected semantics

The native oracle returns `4294967294` for the left shift and `-1` for the
oversized arithmetic right shift. The LCNF interpreter should return the same
signed integers with no effects.

## Actual behavior

The final-impure artifacts import `Int.shiftLeft` and `Int.shiftRight`
directly. The LCNF interpreter stops with `external-failure` because both
declarations are absent from the validation allowlist.

## Proof or differential evidence

The focused run produced four native/LCNF mismatches: positive and negative
left shifts and positive and negative right shifts. Each native observation
returned normally; each LCNF observation reported the corresponding unmodeled
external.

## Semantic impact

The reusable native-oracle comparison infrastructure cannot validate Lean
programs containing signed shifts against the LCNF interpreter or a V8-hosted
semantic Wasm product until the exact runtime contract is modeled.

## Classification and triage

Lean's native results agree with the documented two's-complement shift
semantics, and the final-impure external names are stable and explicit. The
missing behavior is local to the validation adapters, so this is classified as
a validation-harness gap rather than a compiler or interpreter-semantics bug.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Resolved in the same vertical slice by exact `Int → Nat → Int` handlers for
both signed shifts. Lean guards pin positive and negative immediate/heap
transitions, multi-limb results, arithmetic sign extension, and an oversized
multi-limb count. `scripts/test_wasm_validation_externals.mjs` independently
pins the same contract for the V8 semantic host.
