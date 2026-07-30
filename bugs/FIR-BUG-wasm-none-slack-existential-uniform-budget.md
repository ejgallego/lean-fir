---
id: FIR-BUG-wasm-none-slack-existential-uniform-budget
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 608aaaf148ceac3380330ea2eb218c495ee45a56
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-07-31
reproduction: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean
regression: integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean
---

# Summary

The slack-parametric structural theorem returned a separate existential target
post-store for each budget, while the hereditary declaration contract requires
one fixed post-store satisfying every admissible residual budget.

## Minimal reproduction

Instantiate
`codeWP_of_reuseCapacityBudgetedCodeEvaluates_entryRelativeWithSlack` once at
zero slack to select a declaration result store, then instantiate it again at
an arbitrary caller budget. The second theorem supplies the desired residual
`AddressSpaceBudget`, but initially at a newly existentially quantified store;
the former interface supplied no theorem identifying that store with the
zero-slack result.

## Exact commands

```text
make talos-setup
make talos-check
```

The compiler-correctness contract guards the resulting cache-aware hereditary
declaration and ABI refinement surface.

## Expected semantics

Deterministic Wasm execution from one initial configuration has one exact
return endpoint. Re-running the structural proof with more resource slack
should provide stronger resource evidence for that same execution result.

## Actual behavior

The resource theorem was correctly parametric in slack, but its existential
packaging did not expose endpoint equality. It therefore could not directly
construct the universal `residualBudget` field for a declaration with a fixed
`afterCall`.

## Proof or differential evidence

The zero-slack and arbitrary-slack conclusions each contain a `CodeWP` with an
`ExactReturnControlPost`. Unfolding `Wasm.wp` exposes executions of the same
deterministic `Wasm.exec`; comparing both at the maximum of their sufficient
fuel bounds proves equality of the returned store and physical value.

## Semantic impact

No runtime discrepancy is known. The missing proof bridge blocked construction
of the recursive hereditary declaration theorem and made the roadmap
incorrectly claim that slack preservation alone supplied fixed-endpoint budget
uniformity.

## Classification and triage

This is a W6 proof-interface gap. The resource-indexed structural theorem is
sound and remains unchanged; the repair adds exact-return uniqueness and a
packager rather than weakening the callee contract or adding execution
certificates.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

`CodeWP.exactReturn_unique` identifies the endpoints of any two exact-return
proofs for the same target configuration.
`ConcreteReuseCapacityCacheFrame.withBudget` reinstantiates the canonical frame
at arbitrary slack, and
`budgetedDeclarationWithCache_of_reuseCapacityBudgetedCodeEvaluates` combines
both facts into one cache-aware budgeted declaration package. The compiler
contract additionally guards caller-facing ABI refinement through
`BudgetedCapacityPreservingSuccessfulDeclarationWithCache.ofRefines`.
