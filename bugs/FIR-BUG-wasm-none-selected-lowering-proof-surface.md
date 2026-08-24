---
id: FIR-BUG-wasm-none-selected-lowering-proof-surface
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: 94108ba06cde5d03d3320ccf759196ce9c8a347c
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-08-24
reproduction: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean
regression: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean
---

# Summary

The selected-closure lowering refactor hides the declaration and module
lowering bodies behind private helpers, so fresh W6 elaboration cannot recover
the production equations used by the compiler-correctness proof.

## Minimal reproduction

On W7 head `a0e7d161`, force a fresh elaboration of
`ConcreteReuseCapacityCacheCorrectness.lean`. The existing proofs unfold the
public `Fir.Wasm.lowerDecl` and `Fir.Wasm.lower` entry points, but reduction
stops at inaccessible private constants
`lowerDeclWithClosureCandidates` and `lowerWithClosureTargetFilter`.

## Exact commands

```text
make talos-setup
lake -d integration/talos build +FirTalos.ConcreteReuseCapacityCacheCorrectness
```

The direct build is required: an aggregate `make talos-check` can replay the
pre-refactor proof olean and appear green.

## Expected semantics

Refactoring generic lowering through a selected-target implementation should
retain public proof-facing equations for the declaration traversal, function
table, imports, initializers, and declaration-local compilation context.

## Actual behavior

Fresh elaboration fails in
`LazyCacheGeneratedEnvironment.initializers_of_lower`,
`LoweredInternalDeclaration.exists_of_lowerDecl`,
`lowerDecl_some_of_code`, `functions_of_lower`, `functionNamesNodup`, and
`imports_of_lower` because the private implementation bodies cannot be
unfolded from W6.

## Proof or differential evidence

The first direct failure is `dsimp made no progress` after unfolding
`Fir.Wasm.lower`; later goals display an inaccessible private declaration.
The same forced build also exposed the intended selected-candidate equality
changes, confirming that the previously reported 3,171/3,172 Talos result was
partly stale-oLean evidence.

## Semantic impact

No runtime mismatch is currently known, but the generation candidate cannot
receive a clean proof handoff or support the selected-lowering whole-module
theorem while its compiler equations are inaccessible.

## Classification and triage

This is a shared compiler/proof-surface regression. W7 should expose the
implementation helper or public characterization equations; W6 should then
consume that surface rather than duplicate the lowering implementation.

## Workaround

None. W6 must not copy the private lowering body into a parallel proof-side
definition.

## Upstream tracking

W7-W6-20260823-008

## Resolution and regression

Resolved by W7 commit `94108ba0`, which makes
`lowerDeclWithClosureCandidates` and `lowerWithClosureTargetFilter`
proof-visible without adding a parallel lowering or changing their executable
behavior. W6 unfolds those production helpers explicitly, normalizes the
generic `none` selection to the public `lowerDecl` equation where needed, and
retains the existing function-table, import, initializer, and declaration
correctness statements.

The permanent regression is forced direct elaboration of
`ConcreteReuseCapacityCacheCorrectness.lean` before accepting the aggregate
Talos gate. The repaired proof passed Lean Beam refresh/save with zero errors
and `lake build +FirTalos.ConcreteReuseCapacityCacheCorrectness` rebuilt the
module successfully on the selected-lowering stack.
