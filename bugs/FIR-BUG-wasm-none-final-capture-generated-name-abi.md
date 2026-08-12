---
id: FIR-BUG-wasm-none-final-capture-generated-name-abi
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: source-closure-test
first-seen: 2026-08-12
reproduction: Fir/Wasm/Emit/SourceExamples.lean
regression: Fir/Wasm/Emit/SourceClosedFixture.lean
---

# Summary

Recompiling an imported declaration through FIR's generic final-LCNF capture
can associate a freshly generated closed term with the ABI of a different
closed term from the declaration's original module compilation. The first
production witness was `Zip.Native.Deflate.distCodeWordBytes._closed_2`, where
a generated `USize` binding was assigned the imported `UInt8` signature.

## Minimal reproduction

`SourceClosedFixture.wordTable` first seeds Lean's imported specialization and
closed-term caches. `packedTable` repeats the map and folds the result into a
ByteArray. Ordinary module compilation and isolated source recompilation then
extract the closed terms in different orders.

## Exact commands

```sh
lake build Fir.Wasm.Emit.SourceClosedFixture Fir.Wasm.Emit.SourceExamples
```

The unpatched compiler fails while recompiling `packedTable`:

```text
failed to compile definition, compiler IR check failed at
`Fir.Wasm.Emit.SourceClosedFixture.packedTable._closed_2`.
Error: unexpected type 'u8', object expected
```

The same error occurs for the real lean-zip Level-1 closure:

```text
Zip.Native.Deflate.distCodeWordBytes._closed_2:
unexpected type 'u8', object expected
```

## Expected semantics

Every synthetic final-LCNF compilation unit owns the generated closed-term and
specialization names it creates. A freshly generated declaration must resolve
references against signatures from that same unit.

## Actual behavior

Generated names retain their imported module indices. LCNF phase lookup
therefore prefers the imported signature over the newly generated local
signature when the same name denotes a different closed term after extraction
order changes.

## Proof or differential evidence

The repository-native regression fails on `main` at `3f7bcbc8` and passes with
the repair. The real lean-zip source modules also compile normally under the
same Lean 4.33 toolchain; only isolated final-LCNF recompilation failed.

## Semantic impact

Valid imported Lean declarations containing repeated static tables cannot be
captured as isolated final LCNF. The failure happens before FIR lowering and
blocks the real `Zip.Wasm.compressLevel1` closure inventory.

## Classification and triage

This is a generic source-capture ABI defect. It is not a ByteArray resident
runtime discrepancy and not a reason to fall back to Lean IR.

## Workaround

None. Copying the source function, retaining the table as an undocumented host
external, or accepting the malformed ABI would violate the compilation
contract.

## Upstream tracking

none

## Resolution and regression

Before each isolated compiler run, FIR now forgets imported module mappings
only for generated closed terms and cached specializations belonging to the
modules being recompiled. It then clears both caches. Ordinary source and
runtime declarations retain their module mappings. LCNF lookup consequently
falls back to the fresh local generated signature while all unrelated imported
compiler declarations remain available.
