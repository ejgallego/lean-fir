---
id: FIR-BUG-wasm-none-float-external-nan-canonicalization
status: confirmed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-07-30
reproduction: Fir/Validation/Corpus.lean#float32-of-bits-nan-payload
regression: scripts/wasm_validation_externals.mjs
---

# Summary

The V8 validation registry preserves NaN payload/sign bits returned by
floating externals, while native Lean 4.32 canonicalizes those external
results to the positive quiet NaN for the destination width.

## Minimal reproduction

Run `Float32.ofBits 0x7fc12345`, `Float.ofBits 0x7ff8123456789abc`, or divide
positive zero by positive zero. Native and LCNF return `0x7fc00000` for
`Float32` and `0x7ff8000000000000` for `Float`. The V8 registry returns the
input payload for `ofBits`; its JavaScript arithmetic path can also retain a
different NaN sign.

## Exact commands

```sh
python3 scripts/validate_interpreters.py \
  --plan validation-plans/native-lcnf-v8-scalars.json \
  --tag float \
  --out-dir _build/validation-v8-float
```

The run executes all 67 selected cases and reports exactly four mismatching
case IDs across the native/V8 and LCNF/V8 comparison pairs.

## Expected semantics

Manifest parsing and ABI transport retain the supplied raw bits. A call to a
Lean floating external is a separate semantic boundary: if its result is NaN,
the validation implementation returns the positive quiet NaN of the result
width, matching native Lean 4.32.

## Actual behavior

The registry's floating codec re-encodes the JavaScript `Number` bit pattern,
and `ofBits` bypasses that codec entirely. Payload and sign therefore depend on
the input or JavaScript engine rather than Lean's observed result.

## Proof or differential evidence

All non-NaN float cases, including signed zero, infinities, subnormals,
overflow, comparisons, conversions, packed layouts, boxes, and mixed closure
captures, agree across native, LCNF, and V8. Only the four NaN-producing
external cases disagree.

## Semantic impact

Bit-exact manifests remain correct, but external-call observations are not
differentially faithful and can vary by JavaScript engine.

## Classification and triage

This is an adapter implementation gap. Canonicalization belongs inside the
Lean external registry, not in manifest parsing or the generic f32/f64 ABI
encoder/decoder.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Unresolved.
