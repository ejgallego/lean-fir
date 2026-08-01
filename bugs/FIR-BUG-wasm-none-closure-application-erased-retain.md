---
id: FIR-BUG-wasm-none-closure-application-erased-retain
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: dbd7d934
phase: wasm
pass: none
discovered-by: refinement-proof
first-seen: 2026-08-01
reproduction: Fir/Wasm/Concrete/ClosureRuntime.lean
regression: Fir/Wasm/Concrete/OwnershipFrameCorrectness.lean
---

# Summary

Shared closure application retains each transferred owning capture. An erased
capture is semantic ownership data represented by physical word zero: the
semantic `retainOwnedValue` operation is a no-op, but the concrete
`incrementReference` primitive rejects the sentinel as `expectedObject`.

## Minimal reproduction

Construct a shared closure whose capture descriptor contains `.erased`, then
run `takeClosureApplication`. The ownership decoder returns word zero and the
subsequent ordinary increment fails even though the corresponding semantic
application succeeds without changing that capture.

## Exact commands

```text
lake build Fir.Wasm.Concrete.OwnershipFrameCorrectness
make talos-check
```

## Expected semantics

Closure-application transfer treats non-heap owned values as retain no-ops.
This is specific to transferring an already typed owned slot; ordinary
unchecked or checked reference increment keeps rejecting physical zero.

## Actual behavior

The initial concrete implementation reused `incrementReference` directly for
every decoded owning word. Its sentinel branch reports `expectedObject`, so a
well-related erased fixed argument breaks the application refinement.

## Proof or differential evidence

`OwnershipValueRel` admits `.erased` through the ABI ownership filter, while
the proposed shared-application fold cannot establish a concrete no-op for
word zero using the ordinary increment contract.

## Semantic impact

Without an operation-specific boundary, concrete/Talos execution can trap on
a source application that succeeds. Weakening ordinary object decoding would
hide the mismatch and accept invalid standalone increment calls.

## Classification and triage

This is a concrete runtime adapter bug in the closure-application ownership
boundary. The source contract at `dbd7d934` is internally consistent.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

The closure-application boundary now uses `retainClosureCapture`, which maps
physical zero to an exact no-op while preserving strict `incrementReference`
for ordinary calls. `OwnershipValueRel.retainClosureCaptureStep`, the ordered
capture-fold refinement, and `LiveHeapRel.takeClosureApplication_refines`
cover the erased, persistent, exclusive, and shared cases. The direct concrete
theorem build and `make talos-check` are the permanent regression gates.
