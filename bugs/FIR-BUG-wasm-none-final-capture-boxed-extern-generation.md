---
id: FIR-BUG-wasm-none-final-capture-boxed-extern-generation
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: source-closure-test
first-seen: 2026-08-12
reproduction: integration/lean-zip/ProbeLevel1.lean
regression: integration/lean-zip/ProbeLevel1.lean
---

# Summary

FIR's recursively internalized final-LCNF source closure leaves upstream
compiler-generated boxed adapters for imported extern declarations unresolved,
even though Lean's public explicit-boxing pass can regenerate them from the
real extern signatures.

## Minimal reproduction

Capture and link the real `Zip.Wasm.compressLevel1` closure after private
specialization capture is repaired. The complete remaining import frontier is:

```text
UInt8.ofNat._boxed
UInt32.ofNat._boxed
UInt8.toNat._boxed
```

## Exact commands

From `integration/lean-zip`, run the source-view setup documented in its
README, then:

```sh
lake env lean ProbeLevel1.lean
```

Inspect `remainingImports` in `_build/level1-probe.json`.

## Expected semantics

When an unresolved name is `base._boxed` and `base` is a real extern, source
capture should compile the extern declaration through Lean's ordinary LCNF
pass manager. `LCNF.ExplicitBoxing.addBoxedVersions` then creates the adapter
using the exact raw signature and standard `box`/`unbox` operations.

## Actual behavior

Final source-root discovery rejects all extern declarations. That is correct
for ordinary calls whose native operation belongs at the resident boundary,
but it also prevents the generic compiler pass from producing the derived
boxed adapter.

## Proof or differential evidence

The Level-1 probe requires all three upstream-generated adapters to be local.
After regeneration through `ExplicitBoxing`, it reports zero unsupported
declarations and links the complete artifact with zero imports and zero
remaining runtime operations, without a named resident shim.

## Semantic impact

Otherwise self-contained Wasm applications retain host imports whenever a
closure or object-family call reaches a fixed-width extern through its boxed
ABI. Handwritten resident shims would duplicate upstream compiler policy and
would require a declaration-name catalog.

## Classification and triage

This is a generic final-LCNF capture omission. It is not a missing UInt8,
UInt32, Nat, or ByteArray runtime operation: all raw operations and scalar
boxing primitives are already resident.

## Workaround

None. The `_boxed` names are not implemented by a resident helper table.

## Upstream tracking

none

## Resolution and regression

Final source-root discovery now recognizes `base._boxed` only when `base` is a
real code-generating extern, then recompiles `base` through Lean's ordinary
LCNF pass manager. `LCNF.ExplicitBoxing.addBoxedVersions` generated all three
adapters; FIR does not synthesize their bodies or encode their signatures.

That exposed the adapters' actual raw boundary:

```text
UInt8.toBitVec  : uint8  → tobject
UInt8.ofBitVec  : tobject → uint8
UInt32.ofBitVec : tobject → uint32
```

The generic fixed-width resident layer internalizes those representation
externs using its existing checked `toNat32Function`/`ofNat32Function`
machinery. `ProbeLevel1.lean` now requires zero imports and zero runtime
operations and fails instead of merely recording a nonempty frontier.

The repaired real source closure captures 429 declarations with 108 reviewed
externals and zero unsupported declarations. It links 1908 functions with zero
imports and zero runtime operations; the confirming run took 49958ms to
capture, 3428ms to lower, and 4222ms to link.
