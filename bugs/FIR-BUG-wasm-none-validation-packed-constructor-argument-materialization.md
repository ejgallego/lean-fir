---
id: FIR-BUG-wasm-none-validation-packed-constructor-argument-materialization
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-08-13
reproduction: Fir/Validation/Corpus.lean
regression: Fir/Validation/Corpus.lean
---

# Summary

Validation input encoding materializes every constructor field in the object
field vector, including `USize` and fixed-width scalar fields that Lean stores
in packed constructor lanes.

## Minimal reproduction

Compile a one-argument entry whose structure contains two `ByteArray` fields,
one `USize`, and one `UInt32`. Encode the corresponding validation constructor
with schemas `[bytes, bytes, usize, bits 32]`.

## Exact commands

```text
python3 scripts/validate_interpreters.py \
  --plan validation-plans/native-lcnf-v8-scalars.json \
  --case effect-record-nested-aliased-byte-array-layout
```

The original mixed-layout probe failed in V8 before invocation with
`constructor object-field arity mismatch`; native and LCNF agreed.

## Expected semantics

The initial semantic constructor uses two object fields, one USize field, and
one packed `UInt32` scalar field, matching the final-LCNF constructor layout.

## Actual behavior

`Fir.Validation.Lcnf.encodeDatum` calls `allocCtor` with all four encoded
values as object fields and declares zero USize/scalar lanes. The Wasm decoder
correctly rejects that initial runtime against the mixed constructor schema.

## Proof or differential evidence

The rejected manifest contained four entries under `objectFields`, including
values tagged `usize` and `scalar`, while `semanticDatum` derived a two-object,
one-USize, one-scalar layout from the schema.

## Semantic impact

Corpus-driven Wasm invocations cannot yet use mixed-layout structure inputs,
even when the generated entry itself supports their ABI.

## Classification and triage

This is independent of nested alias identity. The constructor encoder needs a
schema-derived packed layout and must populate `ConstructorObject` lanes rather
than routing packed fields through the generic object vector.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

The validation encoder and decoder now derive constructor storage from the
same logical schema convention used by the generated-Wasm runner. Reference
fields retain source order in the object vector, `USize` fields retain source
order in their own vector, and packed scalars use Lean's descending-width byte
groups while preserving source order within each width.

`effect-record-nested-aliased-byte-array-mixed-layout` transfers and returns a
real structure containing two aliased `ByteArray` fields, one `USize`, and one
`UInt32`. Its first array is updated through copy-on-write while native Lean,
the LCNF interpreter, and V8 agree on the untouched alias and both packed
values. A Lean round-trip guard additionally covers all supported integer and
floating packed widths in deliberately interleaved source order.
