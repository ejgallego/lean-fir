---
id: FIR-BUG-wasm-none-nested-input-alias-materialization
status: candidate
classification: validation-harness
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-08-13
reproduction: Fir/Validation/Corpus.lean
regression: none
---

# Summary

The validation input format represents nested constructor and sequence values
as trees, so it cannot state that two child positions are the same Lean heap
object. Generated Wasm therefore receives equal-but-distinct children even
when the native fixture shares one object.

## Minimal reproduction

Pass a constructor whose two `ByteArray` fields reference one source array to
an entry that mutates the first field and returns both fields. The initial
child must have reference count two so Lean's copy-on-write path leaves the
second field unchanged.

## Exact commands

```text
lake build Fir.Validation.Corpus Fir.Wasm.Emit.SourceExamples
```

After admission, the external validation gate must run the fixture through
native Lean, the LCNF interpreter, and generated Wasm in V8.

## Expected semantics

Input graph identity is preserved recursively. Every extra owning edge to a
shared nested object increments its initial reference count exactly once.

## Actual behavior

`ValidationDatum` describes only a value tree and the existing
`ArgumentAlias` contract names only complete argument roots. Nested equal
values are independently allocated.

## Proof or differential evidence

The current compiler manifest has no backend-neutral metadata from which the
LCNF or Wasm materializer can construct a shared nested child.

## Semantic impact

Entries that branch on uniqueness, including destructive `Array` and
`ByteArray` operations, can take a different copy-on-write path in generated
Wasm than in native Lean.

## Classification and triage

The first missing surface is the shared validation contract. W7 then needs to
consume the validated path graph during initial heap construction and the V8
runner must verify locations and reference counts before execution.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

pending
