---
id: FIR-BUG-wasm-none-direct-callee-budget-premise
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: dcb7d6b3dc45e7a9911f84f0c2cf22e6bdd0fe02
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-08-08
reproduction: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean
regression: integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean
---

# Summary

The recursive direct-call implementation interface discards the caller's
proved `stepCost ≤ remainingBytes` fact before asking the hereditary callee
theorem to construct an exact-cost target execution.

## Minimal reproduction

Attempt to construct `DirectInternalCallDeclarationInduction` from a generated
callee row, its finite source-body evaluation of cost `stepCost`, and the
canonical caller frame indexed by `remainingBytes`. The existing callee-entry
theorem can re-index the frame at `remainingBytes`, while
`budgetedDeclarationWithCache_of_reuseCapacityBudgetedCodeEvaluates` requires
the entry frame at exactly `stepCost`. Budget monotonicity needs
`stepCost ≤ remainingBytes`, but the declaration-induction interface does not
receive the inequality already available to its caller.

## Exact commands

```text
make talos-setup
make talos-check
```

The compiler-correctness contract will guard the repaired direct-call budget
surface.

## Expected semantics

The structural call theorem checks that the source-selected callee allocation
cost fits the current concrete address-space budget before executing the
callee. The same inequality should be available to the hereditary callee
construction so it can weaken the caller frame to the callee's exact required
budget.

## Actual behavior

`ReuseCapacityCallLetRuntimeRefinesWithCost` receives
`stepCost ≤ remainingBytes`, but
`DirectDeclarationCallImplementationWithCache.runtimeRefinesEntryRelative`
omits it when invoking `DirectDeclarationCallImplementationWithCache`.
Consequently `DirectInternalCallDeclarationInduction` is asked for a target
execution even when its stated premises do not establish sufficient concrete
address space.

## Proof or differential evidence

The first production-backed hereditary induction step reaches the obligation
to construct a `ConcreteReuseCapacityCacheFrame` indexed by `stepCost` from
the generated callee-entry frame indexed by `remainingBytes`. The only missing
fact is precisely the `stepFits` hypothesis in the enclosing structural call
law.

## Semantic impact

No compiler or runtime mismatch is known. The overstrong proof interface
blocks the certificate-free recursive compiler theorem and obscures the real
resource precondition of target execution.

## Classification and triage

This is a W6 Wasm proof-interface defect. The allocation-cost semantics and
the structural runtime law already carry the correct condition; the repair is
to preserve that condition through the implementation and module-induction
interfaces.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

`DirectDeclarationCallImplementationWithCache` and
`DirectInternalCallDeclarationInduction` now retain the enclosing structural
call's `stepCost ≤ remainingBytes` premise.
`ConcreteReuseCapacityCacheFrame.generatedDirectCalleeEntryAtCost` uses that
fact to weaken the caller-owned address-space budget to the exact callee cost,
and the compiler contract applies this public boundary directly.
`ConcreteGeneratedInternalDeclaration.targetParameterCount` proves the
production physical row has the adapted target arity, while
`budgetedDeclarationWithCache_of_reuseCapacityBudgetedCodeEvaluates` combines
the exact-cost entry with a finite source-body evaluation and uniform runtime
laws to produce the hereditary declaration package.
