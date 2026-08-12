---
id: FIR-BUG-wasm-none-prop-outcome-proof-irrelevance
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: 393ce78e
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-08-12
reproduction: integration/talos/FirTalos/ConcreteResumableWasm.lean
regression: integration/talos/FirTalos/ConcreteStructuredSimulation.lean
---

# Summary

`ConcreteStructuredCodeStepOutcome` is proof-valued, so indexing its supported
resource graph by an outcome proof cannot retain the outcome constructor under
Lean's proof irrelevance.

## Minimal reproduction

Attempt to derive `ConcreteStructuredRunnableOutcome` by first eliminating a
`ConcreteStructuredCodeStepOutcome` and then its
`ConcreteStructuredCodeStepOutcome.OwnsResourceStack` witness. Lean generates
cross-product branches such as a returned outcome paired with the
`directReady`, `saturatedReady`, or external resource constructors.

## Exact commands

```text
cd integration/talos
lake build FirTalos.ConcreteResumableWasm
```

## Expected semantics

The strong supported relation must retain exactly which of ordinary code,
direct/saturated call readiness, external readiness/bind, or returned control
is active, together with the resource stack owned by that same branch.

## Actual behavior

All proofs of the `Prop`-valued outcome are definitionally irrelevant for
dependent elimination. The `OwnsResourceStack` graph therefore cannot be used
as a sound branch-identity package, despite having one constructor per outcome
shape.

## Proof or differential evidence

The current-step classifier proof produces goals named
`returned.directReady`, `returned.saturatedReady`,
`returned.externalReady`, and `returned.externalBind`, and cannot transport
the selected supported stack to the actual branch resources.

## Semantic impact

The executable compiler and runtime are unaffected. The strong W6 relation is
too permissive to support the intended branch-exact finite-trace simulation,
so `ConcreteFiniteTraceCorrect` cannot soundly be closed through that package.

## Classification and triage

This is a W6 refinement-relation design bug. Replace the proof-indexed graph
with a direct branch-exact supported control sum whose constructors contain
their own aligned supported/resource evidence.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

`ConcreteStructuredSupportedOutcome` is now a direct branch-exact inductive
sum. Each constructor owns its own compiler/resource relation, supported frame
stack, and agreement proof. `ConcreteStructuredRunnableOutcome.code` also uses
the same fact and byte-budget indices as its pointwise relation, so the global
classifier packages canonical witnesses rather than unconstrained indices.

Direct builds of `FirTalos.ConcreteStructuredSimulation` and
`FirTalos.ConcreteResumableWasm` exercise the regression.
