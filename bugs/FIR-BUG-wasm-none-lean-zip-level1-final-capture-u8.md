---
id: FIR-BUG-wasm-none-lean-zip-level1-final-capture-u8
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

Single-unit final-LCNF capture of the real
`Zip.Wasm.compressLevel1` closure fails Lean's compiler IR check at the
generated closed term `Zip.Native.Deflate.distCodeWordBytes._closed_2`:
a captured `UInt8` value is supplied where an object is expected.

## Minimal reproduction

Build the read-only lean-zip and zipCommon source views with
`compiler.postponeCompile=true`, then ask FIR's
`compileEntriesFinalCapturedInternalized` path to capture
`Zip.Wasm.compressLevel1`.

## Exact commands

```sh
cd integration/lean-zip
lake --keep-toolchain --reconfigure \
  -KleanZipRoot=/tmp/fir-lean-zip-30737 \
  -KzipCommonRoot=/tmp/fir-zip-common-4425 \
  build LeanZipFir.Compile
lake --keep-toolchain env lean ProbeLevel1SingleUnit.lean
```

## Expected semantics

The final-LCNF capture preserves Lean's generated closed-term ABI and returns
the reachable Level-1 declaration/external inventory. Fixed-width scalar
captures retain their unboxed representation.

## Actual behavior

Lean rejects the reconstructed compiler input before FIR lowering:

```text
failed to compile definition, compiler IR check failed at
`Zip.Native.Deflate.distCodeWordBytes._closed_2`.
Error: unexpected type 'u8', object expected
```

## Proof or differential evidence

The real source modules elaborate and build successfully under the same Lean
4.33 FIR toolchain. Failure occurs only when the recursively discovered roots
are recompiled as one synthetic final-LCNF unit.

## Semantic impact

FIR cannot inventory or lower the real Level-1 compressor through the
single-unit capture path, so missing resident operations cannot yet be
distinguished from capture failures.

## Classification and triage

This is a final-LCNF source-capture ABI discrepancy, not a resident ByteArray
runtime failure. The generated `_closed_2` name suggests that synthetic-unit
closed-term reconstruction lost a fixed-width capture convention.

## Workaround

None. The module-wise API cannot be used for this legacy source view because
its oleans contain no deferred compiler groups.

## Upstream tracking

none

## Resolution and regression

The shared repair in
`FIR-BUG-wasm-none-final-capture-generated-name-abi` makes each isolated
final-LCNF run forget imported module mappings for generated closed terms and
specializations in the modules being recompiled, then clears those caches.
The public generic API now captures this real entry as 391 declarations and
110 externals. The probe reaches FIR lowering, where its next frontier is the
independent `List.MergeSort.Internal.mergeTR.go` admission case.
