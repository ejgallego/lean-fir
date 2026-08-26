---
id: FIR-BUG-wasm-none-float32-resident-boxing
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: source-closure-test
first-seen: 2026-08-26
reproduction: Fir/Wasm/Emit/ResidentFloat.lean
regression: Fir/Wasm/Emit/ScalarBoxingExamples.lean
---

# Summary

W7 has a heap-only resident box/unbox path for `Float` but not for the equally
heap-only compiler-emitted `Float32` family.

## Minimal reproduction

Compile a no-inline polymorphic identity specialized to `Float32`:

```lean
@[noinline] def polyId (alpha : Type) (value : alpha) : alpha := value
def float32Entry (value : Float32) : Float32 := polyId Float32 value
```

Base lowering produces exactly `.box .float32 .object` and
`.unbox .float32`.  Applying the ordinary closed resident policy with
`requireNoRuntimeOperations := true` fails with
`resident linker left 2 runtime operation(s)`.

## Exact commands

Inspect the upstream and resident inventories:

```sh
sed -n '2880,2900p' \
  /home/egallego/.elan/toolchains/leanprover--lean4---v4.33.0/include/lean/lean.h
sed -n '130,230p' Fir/Wasm/Emit/ResidentFloat.lean
```

The seven-family probe result is recorded in
`Fir/Wasm/Emit/SCALAR_BOXING_CONFORMANCE.md`.

## Expected semantics

`Float32` boxing allocates an ordinary owned heap object, stores all 32 input
bits without numeric canonicalization, and returns an exact `object`.
Unboxing checks that layout and reloads the exact `f32` bits.  The linked
module has no import or residual runtime operation for the pair.

## Actual behavior

`ResidentFloat.runtimeName?` and `runtimeFunction` recognize only
`.box .float .object` and `.unbox .float`.  No W7 helper or stable W6
resident-box descriptor exists for `Float32`.

The audit also found that the existing Float-only W7 helper stores marker `6`,
while the executable concrete host's reviewed scalar layout reserves `6` for
`Float32` and `7` for `Float`.  The standalone resident-float artifact did not
exercise either box/unbox operation, so it could not detect the marker drift.
This must be repaired together with the missing Float32 helper rather than
assigning another W7-private code.

## Proof or differential evidence

The otherwise identical `Float` generic identity links to zero imports and
zero runtime operations.  The `Float32` entry lowers successfully, isolating
the failure to resident helper selection rather than source capture,
admission, or scalar ABI support.

## Semantic impact

Pure Lean programs that move `Float32` through a generic container, generic
call, or generated boxed function cannot become self-contained resident Wasm.

## Classification and triage

This is W7 executable-helper coverage with a dependent W6 layout/refinement
surface.  Reuse the existing heap-only Float construction pattern, but route
the four-byte marker and canonical header through W6 before claiming the
linked helper theorem.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

`ResidentFloat` now internalizes `.box/.unbox .float32` and aligns both
floating markers with the concrete-host inventory (`Float32 = 6`,
`Float = 7`). Both boxes allocate one canonical 40-byte owned object;
Float32 zeroes the upper half of its semantic slot, and both checked unboxers
validate the complete header before reinterpreting the stored bits.

The permanent source fixture requires generic and compiler-generated
`Float32` wrappers to link with zero imports and zero residual runtime
operations. The standalone Node client passes binary32/binary64 signed zero,
subnormal, finite maximum, infinity, quiet-NaN, and signaling-NaN payloads
through integer-lane Wasm façades without a JavaScript numeric round trip. It
also checks exact 40-byte frontier growth, rewind, header markers and widths,
zero Float32 padding, and malformed-width/padding/marker traps. W6 promotion
of the now-stable floating layout into its proved descriptor table remains a
separate refinement checkpoint.
