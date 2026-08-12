---
id: FIR-BUG-wasm-none-persistent-big-numeric-validation
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-08-12
reproduction: integration/lean-zip/level1-smoke.mjs
regression: integration/lean-zip/level1-smoke.mjs
---

# Summary

The arbitrary-precision numeric validator rejects a canonical persistent big
Natural produced by Lean's lazy-constant publication protocol.

## Minimal reproduction

Compile and call `Zip.Wasm.compressLevel1` with any input of at least three
bytes. Its addressability guard evaluates the closed constant
`2 ^ System.Platform.numBits`. Arena preparation constructs that value afresh
and the existing cache-publication helper marks it persistent. The next
`Nat.decLt` traps while validating the constant.

## Exact commands

```sh
cd integration/talos/artifact
lake exe fir-wasm-artifact resident-big-numeric _build/resident-big-numeric.wasm
node run-resident-big-numeric.mjs _build/resident-big-numeric.wasm
```

## Expected semantics

An arbitrary-limb Natural remains a valid Natural after Lean's cache protocol
marks it persistent. Persistent ownership changes reference-count behavior,
not the numeric value or limb layout.

## Actual behavior

`fir_big_numeric_validate_natural` accepts arbitrary-limb Naturals only when
their ownership is ordinary. The observed value has the canonical persistent
header `(kind = natural, flags = live+persistent, rc = 0, marker = bigNatural,
count = 2)` and is rejected before comparison.

## Proof or differential evidence

V8 traps in the second operand validation of `fir_big_ext_Nat_decLt`. A
disposable instrumented module records the rejected address and its header;
the limbs encode `2^64` exactly. The native Lean oracle returns normally.

## Semantic impact

Any closed application comparing or calculating with a cached Natural wider
than the promoted-tag range can trap. The same ownership restriction is
present on arbitrary-limb Integer validation.

## Classification and triage

This is a resident-runtime ownership validation discrepancy. The arena cache
rewrite correctly reuses Lean's generic persistence publication path; numeric
validation must accept both canonical ordinary and canonical persistent
ownership states.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Arbitrary-limb Natural and Integer validation now accepts both canonical
ordinary ownership `(live, rc > 0)` and canonical persistent ownership
`(live+persistent, rc = 0)`, while rejecting other flag/count combinations.
The standalone arbitrary-precision numeric client marks multi-limb Natural and
Integer inputs persistent and exercises the real comparison helpers. The
Level-1 native/Wasm differential covers Lean's closed `2^64` constant through
the complete arena cache-publication path.
