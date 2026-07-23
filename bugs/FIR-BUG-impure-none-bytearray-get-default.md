---
id: FIR-BUG-impure-none-bytearray-get-default
status: fixed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: impure
pass: none
discovered-by: differential-test
first-seen: 2026-07-23
reproduction: Fir/Validation/Corpus.lean#byteArrayGet
regression: Fir/Validation/Corpus.lean#byte-array-get-empty
---

# Summary

FIR's validation runtime faults on an out-of-bounds `ByteArray.get!`, while
native Lean returns the inhabited `UInt8` default value zero.

## Minimal reproduction

Call the noinline validation entry

```lean
def byteArrayGet (value : ByteArray) (index : Nat) : UInt8 :=
  value.get! index
```

with an empty byte array and index zero. The exact-end boundary of a nonempty
array and a heap-natural index exhibit the same discrepancy.

## Exact commands

```sh
python3 scripts/validate_interpreters.py \
  --case byte-array-get-empty \
  --case byte-array-get-end \
  --case byte-array-get-heap-oob \
  --plan validation-plans/native-lcnf.json \
  --out-dir /tmp/fir-byte-array-oob-native-lcnf
```

## Expected semantics

Native Lean is the oracle. All three calls return `UInt8 0`: `get!` supplies
the element type's inhabited default when the requested index is outside the
byte array.

## Actual behavior

`Fir.Validation.LCNF.byteArrayGetExternal` looks up the packed byte with
`value[index]?` and turns `none` into
`RuntimeFault.externalFailure`. The empty, exact-end, and heap-natural cases
therefore fault before final-LCNF reaches `return`.

The real-V8 validation adapter independently rejects an out-of-bounds index in
`scripts/wasm_validation_externals.mjs`, so it implements the same incorrect
boundary policy through a host assertion.

## Proof or differential evidence

The focused matrix reports three semantic mismatches and three corresponding
executed-form failures. Native returns

```text
returned bits[8] 0
```

for indices `0` into `#[]`, `4` into `#[0, 127, 128, 255]`, and
`18446744073709551616` into the same nonempty array. LCNF reports an
`external-failure` with the respective index and array bound.

Retained evidence:

```text
/tmp/fir-byte-array-oob-native-lcnf/evidence/runs/45abfe32e9d95f43c14ff12fd622b3f5048467d66882e7c743ab3ffb9b1801db/fa367f7736573e8ffc70a070d1368114574582065b6c490805ae3d48e2c0f3fa.json
```

## Semantic impact

Any compiler-generated call to `ByteArray.get!` with an out-of-bounds index
observes a validation-only runtime fault instead of Lean's default byte. This
can create false native/LCNF and native/V8 discrepancies and leaves the host
models inconsistent with the runtime primitive they claim to implement.

## Classification and triage

This is a validation semantic-model defect, not a compiler or final-LCNF
lowering defect. The same compiler-produced external call is executed in every
backend, and native Lean consistently supplies the zero default across empty,
exact-end, and heap-index boundaries.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

`Fir.Validation.LCNF.byteArrayGetExternal` and the real-V8 validation external
now return scalar `UInt8 0` when the decoded natural index is outside the
packed byte array. The three `byte-array-get-*` boundary fixtures are the
permanent regression matrix and preserve the existing in-bounds cases.

The focused native/LCNF/V8 run produced nine equal pairwise comparisons with
zero findings:

```text
_build/validation-v8-byte-array-oob/evidence/runs/b3dcdd04b1a865fd5f9cc70f09baa28671a206c6715b8a93486ff673c800b91e/e5a00ec0276334774e39ab3b13e259318d07b6c5a9adbc40fbeb68cdec63d0cc.json
```
