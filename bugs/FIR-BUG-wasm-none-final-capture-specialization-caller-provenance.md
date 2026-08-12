---
id: FIR-BUG-wasm-none-final-capture-specialization-caller-provenance
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

FIR's synthetic final-LCNF dependency discovery recompiles a generated
specialization's generic callee in one growing cross-module unit instead of the
source caller unit that owns the specialization body.

## Minimal reproduction

Capture the real `Zip.Wasm.compressLevel1` source closure. Its imported final
LCNF references these two private compiler declarations:

```text
List.foldl._at_.Array.appendList.spec_0._redArg
List.zipWith._at_.List.zip.spec_0._redArg
```

Lean records their owning modules as `Init.Data.Array.Basic` and
`Init.Data.List.Basic`. FIR's prefix-only lookup instead resolves them to
`List.foldl` in `Init.Prelude` and `List.zipWith` in
`Init.Data.List.Basic`.

## Exact commands

From `integration/lean-zip`, after configuring the source views documented in
its README:

```sh
lake --keep-toolchain env lean ProbeLevel1.lean
```

The focused capture-only Lean Beam probe reports both names in
`source.externalNames` before lowering.

## Expected semantics

Lean constructs specialization names as the specialized declaration followed
by `._at_.`, the current caller declaration, and a `spec_N` component. Source
dependency recovery should compile that caller in an isolated source unit when
the environment confirms the caller and generated helper have the same owner.

## Actual behavior

`environmentDeclarationAncestor?` repeatedly removes the final name component
until it finds a kernel declaration. Because the caller is embedded after the
callee rather than forming a name prefix, this selects the generic callee. FIR
then recompiles all accumulated roots in one synthetic cross-module compiler
unit, unlike Lean's per-module native pipeline. Supplying the correct caller in
that growing unit fails at the stale generated `spec_N` boundary, while
compiling the caller alone captures the corresponding `_redArg` body.

## Proof or differential evidence

The Lean environment reports the generated helpers' module indices and impure
signatures. The embedded `Array.appendList` and `List.zip` names are kernel
source declarations with the same respective module indices. Isolated
final-LCNF capture of `List.zip` produces
`List.zipWith._at_.List.zip.spec_0._redArg` as a local code declaration;
capturing it together with the lean-zip entry fails on the missing private
`spec_0` constant.

## Semantic impact

Valid Lean programs can retain private specialization imports even though the
corresponding source declarations are available. This blocks a self-contained
FIR-native artifact or encourages declaration-specific resident substitutes.

## Classification and triage

This is a generic final-LCNF source-capture provenance and compilation-unit
defect. It is independent of ByteArray, Array, and resident-runtime semantics.

## Workaround

None. Hard-coding the two generated names or treating them as resident helpers
would hide a compiler-boundary error.

## Upstream tracking

none

## Resolution and regression

FIR now decodes Lean's `._at_.<caller>.spec_N` convention with the upstream
name-demangling primitives, validates the embedded caller as compilable source,
and clears only compiler-cache entries owned by the roots being recompiled.
The growing unit adds the caller and generic callee together so Lean's own
specialization pass reconstructs the generated declaration without an imported
stale name or a handwritten specialization.

`ProbeLevel1.lean` rejects every generated specialization left external. On the
fixed path it captures 425 declarations with zero unsupported declarations and
no external specialization names. A caller-only diagnostic variant took
179717ms to capture 384 declarations and retained a runtime operation; restoring
the caller/callee source context took 15421–15567ms and retained none.
