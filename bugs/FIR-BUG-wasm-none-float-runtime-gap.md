---
id: FIR-BUG-wasm-none-float-runtime-gap
status: confirmed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-07-16
reproduction: Fir/LeanIR/Runtime.lean
regression: Fir/Wasm/Examples.lean
---

# Summary

Final impure LCNF includes `Float32` and `Float`, but FIR's abstract impure runtime value model has no corresponding scalar values.

## Minimal reproduction

Lean 4.32's `LCNF.ImpureType` classifies `Float32` and `Float` as impure scalars, while `Fir.LeanIR.Impure.ScalarValue` only contains `UInt8`, `UInt16`, `UInt32`, and `UInt64`.

## Exact commands

Run `lake build Fir.Wasm.Examples`. The ABI guards demonstrate the required `f32` and `f64` projections; inspection of `Fir/LeanIR/Runtime.lean` shows that no source values can currently inhabit those kinds.

## Expected semantics

The shared abstract runtime should represent both floating-point scalar classes so that interpreter observations and Wasm host encode/decode relations cover every impure type.

## Actual behavior

The Wasm ABI and Talos adapter can preserve and project the types, but the FIR interpreter cannot construct, return, or compare corresponding abstract scalar values.

## Proof or differential evidence

The exhaustive ABI-kind table has twelve non-void classes, whereas `ScalarValue` covers only four integer classes and `Value` adds `USize` plus object-like values.

## Semantic impact

Float signatures can be lowered and validated structurally, but float-bearing executions must remain outside differential and correctness claims until the shared runtime is extended.

## Classification and triage

This is a known gap in FIR's shared semantic model. The change belongs to the integration-owned runtime rather than a private Wasm-only value type.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

unresolved
