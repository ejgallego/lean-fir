---
id: FIR-BUG-wasm-none-argument-alias-materialization
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-08-13
reproduction: Fir/Wasm/Emit/SourceExamples.lean
regression: Fir/Validation/Corpus.lean
---

# Summary

The Wasm validation-invocation compiler did not materialize runner-declared
argument aliases as one shared heap root with the corresponding initial
reference count.

## Minimal reproduction

Compile a two-argument `ByteArray` entry with the canonical alias declaration
`0 -> 1`. Both arguments must name the same initial heap location and that
root must have reference count two before the entry runs.

## Exact commands

```text
lake build Fir.Wasm.Emit.SourceExamples Fir.Wasm.Emit.Command
```

After the corpus fixtures are enabled, the repository validation gates exercise
the same invariant through the external V8 runner.

## Expected semantics

The source argument is encoded once, every alias reuses its heap value, and
each additional owned argument increments the shared root exactly once. This
is required for Lean's `isShared` and copy-on-write behavior to agree with
native and LCNF execution.

## Actual behavior

`compileValidationInvocation` accepted only schemas and data, so callers had
no way to pass the validated alias graph into `Fir.Validation.Lcnf.encodeArgs`.
Heap-valued arguments were therefore independently materialized.

## Proof or differential evidence

The compiled validation manifest could not satisfy the invariant that aliased
arguments have identical heap locations and an initial root reference count
equal to their multiplicity.

## Semantic impact

Entries whose behavior depends on uniqueness, including destructive
`ByteArray` and `Array` updates, could take a different copy-on-write path in
generated Wasm than in native Lean.

## Classification and triage

The backend-neutral alias contract and LCNF encoder are correct. The missing
edge is in the W7 validation-invocation adapter, which failed to forward that
contract into initial Wasm heap construction.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

W7 revision `d23ffd02` forwards the canonical alias graph into initial heap
encoding. Revisions `4a5de29a` and `bee07a8e` add the shared-root, multiplicity,
and independent-group corpus fixtures. `Fir/Wasm/Emit/SourceExamples.lean`
also pins manifest location reuse and the exact initial reference count before
external-engine execution.
