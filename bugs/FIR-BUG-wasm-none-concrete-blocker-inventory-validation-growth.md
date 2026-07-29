---
id: FIR-BUG-wasm-none-concrete-blocker-inventory-validation-growth
status: confirmed
classification: validation-harness
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: a669b51d86af72a7de5634b458ccd0f33755ae3b
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-07-29
reproduction: integration/talos/artifact/check.sh
regression: integration/talos/artifact/check-concrete-validation-products.mjs
---

# Summary

The concrete shared-product checker hard-codes the pre-signed-scalar
validation blocker inventory, so a green expanded semantic corpus fails the
artifact gate when newly added scalar cases also carry an unsupported initial
`ByteArray`.

## Minimal reproduction

Run the W7 artifact check from a generation branch whose validation products
include the exact Int32 family. Semantic native/LCNF/V8 comparison succeeds,
then the concrete-product audit reports the added Int32 and conversion cases
as actual blockers absent from `CONCRETE_VALIDATION_BLOCKED_CASES`.

## Exact commands

```sh
bash integration/talos/artifact/check.sh
```

## Expected semantics

The exact blocker inventory tracks every selected validation case whose
compiler manifest requires an initial-runtime `ByteArray` until the concrete
host supports that layout. Adding a semantically green validation family
must update this audited inventory atomically.

## Actual behavior

All selected semantic products compare equal, but
`check-concrete-validation-products.mjs` fails
`concrete validation blocker inventory drifted`. On the pre-rebase W7 branch,
the actual set grows from 33 to 70 cases after the Int32 corpus becomes
visible.

## Proof or differential evidence

The preceding artifact checks pass standalone and linked Wasm execution,
deterministic module/manifest/LCNF generation, package smoke, and all
native/LCNF/V8 semantic comparisons. Only the exact concrete blocker-set
assertion fails, and every added item reports the existing unsupported
initial-runtime `ByteArray` boundary.

## Semantic impact

No semantic mismatch has been observed. The stale inventory prevents a green
W7 artifact gate and can hide whether future validation growth introduces a
new blocker category rather than more cases of the known ByteArray boundary.

## Classification and triage

This is validation-harness drift across the validation and W7 artifact lanes.
The exact inventory should remain explicit; it must be refreshed from the
current selected corpus rather than weakened to accept arbitrary blockers.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Pending rebase onto the complete signed-scalar validation release. The
regression remains the exact-set and ByteArray-category assertions in
`check-concrete-validation-products.mjs`.
