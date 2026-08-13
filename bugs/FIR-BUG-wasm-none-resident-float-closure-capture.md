---
id: FIR-BUG-wasm-none-resident-float-closure-capture
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-08-10
reproduction: integration/illuminate-hit-scene/Emit.lean
regression: Fir/Wasm/Emit/ResidentClosureAllocation.lean
---

# Summary

The resident linker rejects compiler-generated partial applications that
capture a `Float`, even though FIR's closure layout reserves an eight-byte
typed slot and closure dispatch retains the exact capture descriptor.

## Minimal reproduction

Capture and lower `Illuminate.HitScene.query` from clean Illuminate commit
`af088e313eaade90be100aeaf63ddac79a8c1710`, then apply the ordinary W7
closed-application resident policy. The first unsupported descriptor is the
five-value prefix `#[.float, .float, .float, .tobject, .tobject]` captured by
the generated cubic-root traversal closure.

## Exact commands

```sh
cd integration/illuminate-hit-scene
lake --keep-toolchain -KilluminateRoot=/tmp/illuminate-hit-scene-pinned \
  env lean -DmaxHeartbeats=0 Emit.lean
```

## Expected semantics

Partial-application allocation stores the bit-exact binary64 capture in its
eight-byte closure slot. The corresponding typed closure projection reloads
those bits as a Wasm `f64`, exactly as integer and object captures already use
the same descriptor-indexed slot layout.

## Actual behavior

Resident linking stops before external-engine execution with:

```text
failed to internalize resident partial applications:
  ResidentClosureAllocation.LinkError.unsupportedCaptureKind AbiKind.float
```

The linker has the same latent gap for `Float32` captures.

This diagnostic is historical: the fixed implementation no longer retains
the `unsupportedCaptureKind` error constructor.

## Proof or differential evidence

The exact final-LCNF closure has zero unsupported declarations and lowers to
a valid base Wasm module. Its runtime inventory contains Float captures in
`pap_181` and `pap_220`; resident closure allocation alone rejects them.

## Semantic impact

Pure Lean functions that form closures over unboxed floating-point values
cannot become self-contained resident Wasm artifacts. This blocks the real
prepared HitScene query before its 301-query oracle fixture can run.

## Classification and triage

This is a W7 executable-resident-helper omission, not a source lowering or
object-carrier mismatch. The symbolic surface already exposes bit-preserving
`f32`/`i32` and `f64`/`i64` reinterpretation plus typed integer stores and
loads, so no ABI or layout change is needed.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

`ResidentClosureAllocation.captureStore` now preserves `Float32` and `Float`
bits through `i32.reinterpret_f32`/`i64.reinterpret_f64` before storing them in
the existing fixed closure slots. The matching resident projections reload and
reinterpret the exact bits. Standalone mixed-float allocation/projection guards
pass, and the immutable HitScene package exercises the real Float-capturing
closure while passing all 301 queries plus 10,000 repeated calls.
