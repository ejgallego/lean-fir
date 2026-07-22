---
id: FIR-BUG-impure-none-usize-slot-index
status: confirmed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: impure
pass: none
discovered-by: differential-test
first-seen: 2026-07-22
reproduction: Fir/Validation/Corpus.lean#mixedLayoutNatural
regression: Fir/LeanIR/Runtime.lean#absoluteUSizeSlotGuard
---

# Summary

FIR interprets the `uproj` and `uset` coordinate as an index into the
constructor's type-local `usizeFields` array, while Lean final impure LCNF uses
the absolute fixed-slot index after all object fields.

## Minimal reproduction

Construct a structure with three object fields followed by one `USize` field.
Lean 4.32 lowers its constructor to `ctor_0.1.4` followed by `uset object[3]`
and projects the field with `uproj[3]`. FIR allocates one semantic `USize`
entry, then applies absolute slot index `3` directly to that one-element array.

## Exact commands

```sh
python3 scripts/validate_interpreters.py \
  --case mixed-layout-natural \
  --case mixed-layout-usize \
  --plan validation-plans/native-lcnf.json \
  --out-dir /tmp/fir-mixed-native-lcnf
python3 scripts/validate_interpreters.py \
  --verify-matrix /tmp/fir-mixed-native-lcnf/matrix.json
```

## Expected semantics

The native and LCNF observations should agree. For a constructor with three
object fields and one `USize` field, absolute fixed-slot coordinate `3` denotes
`usizeFields[0]`. Lean's `ToImpure.lowerProj`, constructor lowering, and native
C emitter all preserve that absolute coordinate.

## Actual behavior

Native Lean returns the selected source field. FIR faults while executing the
constructor's `uset` with
`RuntimeFault.usizeFieldOutOfBounds 3 1`, before any projection executes.

## Proof or differential evidence

The retained final-impure artifact is:

```text
let value := ctor_0.1.4[MixedLayout.mk] natural text bytes;
uset value[3] := usize;
```

All five projections of the mixed structure return under native Lean and hit
the same FIR runtime fault. Existing `USize` fixtures place their field at
absolute slot zero and therefore did not distinguish absolute from type-local
indexing.

## Semantic impact

Any compiler-produced constructor whose `USize` fields follow one or more
object fields faults in the FIR interpreter. The same coordinate contract is
shared with Wasm lowering and proof-facing host operations, so consumers must
rebase after the integration-owner correction rather than locally translating
the index.

## Classification and triage

This is a FIR semantic-model defect. The compiler artifact, generated native C,
and native observation agree on the absolute fixed-slot coordinate. FIR's
separate `objectFields` and `usizeFields` representation remains usable, but
its accessors must translate the absolute coordinate by the object-field
prefix and reject coordinates outside the `USize` interval.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

The integration-owned runtime now exposes `getUSizeSlot` and `setUSizeSlot`,
which translate Lean's absolute coordinate through the object-field prefix
while retaining type-local semantic storage. The LCNF interpreter and real-V8
semantic host use that contract. `absoluteUSizeSlotGuard` checks a three-object,
one-`USize` layout directly, and the five `mixed-layout-*` differential cases
cover object, `USize`, and scalar projections across native Lean, LCNF, and V8.

The generated Wasm lowering already preserves the correct absolute index and
needs no compiler change. Talos's symbolic and concrete hosts still need to
consume the new slot operation before this card can move from `confirmed` to
`fixed` for every downstream interpreter.
