---
id: FIR-BUG-wasm-none-scalar-projection-index-naming
status: confirmed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-07-20
reproduction: integration/talos/artifact/FirWasmSourceExample.lean
regression: integration/talos/artifact/check.sh
---

# Summary

FIR names the first `sproj`/`sset` coordinate and `ScalarField` key `width`,
but Lean 4.32 final impure LCNF uses that coordinate as the scalar-area slot
index `CtorInfo.size + CtorInfo.usize`, not as the scalar value's byte width.

## Minimal reproduction

Construct the ordinary heap representation of `Std.Format.align false` from
its compiler-derived layout `ctor_2.0.1`: zero object fields, zero `USize`
fields, and one scalar byte. Storing the `UInt8` Boolean under key `(1, 0)`
because it occupies one byte makes the generated pretty-printer request the
missing key `(0, 0)`.

## Exact commands

```sh
cd integration/talos/artifact
lake -d ../../.. env lean FirWasmSourceExample.lean
./check.sh
```

## Expected semantics

The FIR runtime surface should either name the coordinate as a slot index or
provide a constructor-layout helper that derives the correct key. Scalar byte
width remains encoded by `ScalarValue` and by `CtorInfo.ssize`.

## Actual behavior

`LCNF.ToImpure` emits `sproj (ctorInfo.size + ctorInfo.usize) offset`, while
FIR carries the first number through fields and APIs named `width`. For
`Format.align`, the generated host operation is `scalarProj 0 0 uint8` even
though the stored scalar occupies one byte.

## Proof or differential evidence

The all-constructor `Std.Format.prettyM` fixture reached V8 and failed with
`scalarFieldMissing { width: 0, offset: 0 }` when the `align` Boolean was stored
as `{ width: 1, offset: 0, value: uint8(0) }`. The compiler snapshot contains
`ctor_2.0.1[Std.Format.align]` followed by `sset [0, 0]`. Conversely,
`Format.group` has one preceding object field and requests scalar slot one.

## Semantic impact

Compiler-produced programs remain internally consistent, but hand-built
initial-runtime heaps can use the wrong scalar key while appearing to describe
the right byte layout. This affects source fixtures and any future raw host
that constructs Lean constructor objects.

## Classification and triage

This is a FIR semantic-model naming and construction issue. Renaming the
shared runtime coordinate or adding a layout-aware constructor initializer is
integration-owner work because it touches the common runtime contract.

## Workaround

Initial-runtime fixtures use the compiler's scalar slot index—zero for
`Format.align` and one for `Format.group`—and retain the actual `UInt8` width
in the scalar value.

## Upstream tracking

none

## Resolution and regression

The shared naming issue remains unresolved. The Format coverage fixture and
artifact check permanently exercise both affected scalar constructor fields
using their compiler-derived slot coordinate.
