---
id: FIR-BUG-wasm-none-mutual-tail-byte-array-blocker-ratchet
status: fixed
classification: validation-harness
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 642ca30ba7cd2d16dfb3421fcdae3c2b45939394
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-08-25
reproduction: integration/talos/artifact/check.sh
regression: integration/talos/artifact/concrete-validation-case.mjs
---

# Summary

The concrete shared-product checker did not add the new
`shared-byte-array-mutual-tail-three` fixture to its exact ByteArray blocker
inventory when the fixture landed.

## Minimal reproduction

Run the W7 artifact gate after the mutual-tail ByteArray fixture is present.
The 717 native, LCNF, and V8 results all agree, but the concrete-product audit
reports one additional expected ByteArray admission blocker.

## Exact commands

```sh
FIR_BROWSER=google-chrome FIR_PRETTYM_EXHAUSTIVE_CHECKPOINTS=1 \
  bash integration/talos/artifact/check.sh
```

## Expected semantics

The exact blocker inventory includes every selected validation case whose
initial graph contains a ByteArray until the concrete validation host admits
that layout.

## Actual behavior

All 2,151 semantic comparisons pass. The artifact gate then fails
`concrete validation blocker inventory drifted` because the new fixture is
present in the generated products but absent from the audited list.

## Proof or differential evidence

The generated matrix contains 717 successful results for each of native,
LCNF, and V8, with 717/717 equal results for each backend pair and no
findings. The new concrete blocker is an `initial-runtime-object` blocker for
`byteArray`, matching the existing admission boundary.

## Semantic impact

No semantic mismatch was observed. The stale assertion blocks the complete
W7 artifact gate and leaves the exact concrete-admission frontier inaccurate.

## Classification and triage

This is validation-harness drift at the fixture/integration boundary, not a
runtime workaround. Keep the inventory explicit and add only the reviewed
fixture identifier.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

The shared concrete-validation registry now includes the mutual-tail fixture
in its exact ByteArray blocker set. Both the Node and browser artifact checks
consume that registry, so future additions still fail closed.
