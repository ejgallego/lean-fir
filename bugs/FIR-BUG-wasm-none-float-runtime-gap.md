---
id: FIR-BUG-wasm-none-float-runtime-gap
status: fixed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-07-16
reproduction: Fir/LeanIR/Runtime.lean
regression: Fir/Wasm/Examples.lean
---

# Summary

Final impure LCNF includes `Float32` and `Float`; FIR formerly had no
corresponding abstract scalar values and the W6 concrete relation therefore
could not state float execution correctness.

## Minimal reproduction

Historically, `LCNF.ImpureType` classified `Float32` and `Float` as impure
scalars while `Fir.LeanIR.Impure.ScalarValue` contained only the four unsigned
integer widths.

## Exact commands

The historical reproduction was `lake build Fir.Wasm.Examples`, followed by
inspection of `Fir/LeanIR/Runtime.lean`. The current regressions are built by
`make talos-check` and exercise raw-bit float projection and mutation.

## Expected semantics

The shared abstract runtime should represent both floating-point scalar classes so that interpreter observations and Wasm host encode/decode relations cover every impure type.

## Actual behavior

`ScalarValue.float32Bits` and `ScalarValue.float64Bits` now carry the exact
IEEE-754 payloads. `ValueRel`, `PhysicalValueRel`, concrete packed-field
read/write refinement, compiler-step simulation, structured simulation, and
dead-object fault leaves all preserve those payloads in `.f32`/`.f64` lanes.

## Proof or differential evidence

The concrete regressions round-trip Float32 negative zero (`0x80000000`) and a
noncanonical Float NaN payload (`0x7ff8000000000042`) without host floating
conversion. The projection and mutation dependency cones compile under the
six-kind packed-scalar admission.

## Semantic impact

Float packed-field projection and mutation are now inside the W6 correctness
claim. Float boxing/unboxing remains a distinct operation-coverage follow-up;
it is no longer blocked by the abstract semantic value model.

## Classification and triage

The shared semantic change landed through integration ownership. W6 consumes
that representation directly and does not introduce a private Wasm-only float
value type.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Fixed by the shared raw-bit scalar constructors and the W6 exact-lane
refinement slice. Regression coverage lives in
`integration/talos/FirTalos/ConcreteRuntimeExamples.lean`; the full proof gate
is `make talos-check`.
