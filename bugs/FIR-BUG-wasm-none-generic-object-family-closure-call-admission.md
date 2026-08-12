---
id: FIR-BUG-wasm-none-generic-object-family-closure-call-admission
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: source-closure-test
first-seen: 2026-08-12
reproduction: Fir/Wasm/Examples.lean
regression: Fir/Wasm/Examples.lean
---

# Summary

FIR's generated closure dispatcher still requires directional ABI refinement
for applied arguments and target results, even though named calls, joins, and
symbolic stack validation already follow Lean's generic object-family calling
convention.

## Minimal reproduction

Capture and lower the real `Zip.Wasm.compressLevel1` final-LCNF closure. Its
generic `List.MergeSort.Internal.mergeTR.go` applies a heap closure to two
list heads retaining the coarse `tobject` type. The reachable Huffman
comparator lambdas accept two precise `object` parameters.

## Exact commands

```sh
cd integration/lean-zip
lake --keep-toolchain --reconfigure \
  -KleanZipRoot=/tmp/fir-lean-zip-30737 \
  -KzipCommonRoot=/tmp/fir-zip-common-4425 \
  build LeanZipFir.Compile
lake --keep-toolchain \
  -KleanZipRoot=/tmp/fir-lean-zip-30737 \
  -KzipCommonRoot=/tmp/fir-zip-common-4425 \
  env lean ProbeLevel1.lean
```

## Expected semantics

Arguments supplied to an already allocated Lean closure use the same physical
object-family call ABI as named calls and joins. `object`, `tagged`, and
`tobject` are mutually call-compatible; scalar and erased lanes remain exact.
Capture descriptors and semantic refinement remain directional.

## Actual behavior

`supportedClosureCall` and `compileClosureCandidateAt` use `kindsRefine`.
They reject the exact argument pair `[tobject, tobject]` against comparator
parameters `[object, object]`, leaving the merge helper as the sole unsupported
declaration in a 391-declaration source closure.

## Proof or differential evidence

The closure parameter is a heap `object`, both applied arguments are
`tobject`, and the declared comparison result is `tagged`. Using the existing
`AbiKind.leanCompatible` relation resolves exactly the two reachable Huffman
comparator lambdas. Reuse-capacity validation is already true.

## Semantic impact

Valid generic higher-order Lean code can pass named-call admission but fail at
the equivalent closure-call boundary. This blocks Level-1 DEFLATE before the
resident ByteArray frontier can be inventoried precisely.

## Classification and triage

Shared compiler ABI admission. This is the missing closure-dispatch consumer
of the released generic object-family call contract, not a lean-zip-specific
kind rewrite.

## Workaround

None. Do not specialize or restate the merge helper in FIR.

## Upstream tracking

none

## Resolution and regression

`kindsLeanCompatible` now checks only the arguments supplied at closure
invocation. `supportedClosureCall` and `compileClosureCandidateAt` share that
predicate and use `leanCompatible` for the target result. Fixed captures still
use `kindsRefine`, and `AbiKind.refines` remains the directional semantic
relation.

The shared ABI layer records that directional refinement implies call
compatibility, both for one kind and pointwise argument rows. This keeps the
existing Talos closure-resolution hypotheses sufficient without changing any
W6-owned proof contract.

The positive regression applies `[tobject, tobject]` to a comparator target
with `[object, object]` parameters and validates the emitted module. The
negative regression keeps a `UInt32` argument rejected. The real Level-1
witness resolves to `Huffman.Spec.limitedPairsN._lam_1._boxed` and
`Huffman.Spec.limitedPairs._lam_2._boxed` without a source-specific rewrite.
