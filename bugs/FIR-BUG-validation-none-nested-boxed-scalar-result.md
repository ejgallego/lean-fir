---
id: FIR-BUG-validation-none-nested-boxed-scalar-result
status: fixed
classification: validation-harness
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: validation
pass: none
discovered-by: differential-test
first-seen: 2026-08-02
reproduction: Fir/Validation/Corpus.lean
regression: Fir/Validation/Corpus.lean
---

# Summary

The LCNF validation result decoder cannot decode a boxed fixed-width scalar
nested in a generic constructor even though the interpreter executes the
source program to completion.

## Minimal reproduction

Compile a source entry returning `ByteArray × UInt8`, where the `UInt8` is read
from a captured ByteArray through `ByteArray.get!`, and describe the result as
`.ctor "Prod.mk" 0 #[.bytes, .boxed (.bits 8)]`.

## Exact commands

From the fixture worktree at the first S1 probe:

```text
lake --rehash build Fir.Validation fir-native-oracle
python3 scripts/validate_interpreters.py \
  --plan validation-plans/native-lcnf.json \
  --case boxed-byte-array-uint8-input \
  --case captured-byte-array-outside-alias-byte-read \
  --out-dir _build/validation-closure-outside-alias
```

## Expected semantics

Native Lean returns the unchanged ByteArray paired with the byte read at index
zero. Final LCNF boxes the `UInt8` for storage in generic `Prod`, and the
schema-directed result decoder should recover its exact eight-bit value.

## Actual behavior

The LCNF interpreter completes 27 steps, including one `pap`, one `fvar`, one
`ByteArray.get!`, two decrements, two boxes, and the result constructor. Result
decoding then fails with:

```text
cannot decode Fir.LeanIR.Impure.Value.object
  (Fir.LeanIR.Impure.ObjectRef.tagged 0)
  as Fir.Validation.ValidationSchema.bits 8
```

## Proof or differential evidence

Retained run
`c719fe943e1210c2945d72bb170bc75ce211b08d7f4e27d06d281d9dff15d45c`
records the complete successful LCNF execution trace followed by the decoder
failure. The paired ByteArray mutation case agrees with native in the same run.

## Semantic impact

Validation cannot currently expose a fixed-width scalar as a field of a
generic source constructor. This limits otherwise fixture-only ownership tests
and can hide valid interpreter executions behind a protocol failure. It does
not show a discrepancy in the interpreter's closure or ByteArray semantics.

## Classification and triage

This is a validation-protocol coverage gap. The standalone scalar result codec
and generic object-field codec each work, but their composition does not
recognize Lean's boxed generic scalar representation. Repair should be a
separate protocol slice with native/LCNF/V8 consumers coordinated together.

## Workaround

For the compact closure-ownership slice, expose the observed byte as `Nat`,
whose tagged/heap generic-constructor representation is already supported.
Keep this card open rather than importing the historical mixed boxed-scalar
codec into the fixture commit.

## Upstream tracking

None.

## Resolution and regression

The standalone `VALIDATION-BOXED-SCALAR-SCHEMA` contract landed as
`64903ee7`. The LCNF materializer and decoder now apply the runtime's existing
`box` and `unbox` operations at `.boxed` schema nodes, while ordinary scalar
schemas continue to select concrete packed constructor lanes. The semantic
Wasm manifest and JavaScript host also transport boxed initial-runtime cells
and decode tagged or heap boxes without changing the logical datum.

The regression covers both directions: a runner-supplied `ByteArray × UInt8`
tests initial-runtime heap materialization, and a closure-produced
`ByteArray × UInt8` tests returned generic scalar decoding. Both pass native
Lean, the LCNF interpreter, and V8 with exact `UInt8` values.
