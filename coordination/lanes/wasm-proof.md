# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: dcb7d6b3dc45e7a9911f84f0c2cf22e6bdd0fe02 on main
functional-head: e05c9110cf302c9b850be5583a4dc01ae1a925f7
contract-base: dcb7d6b3 on main; consumes the accepted generated-callee entry frame plus the existing budget, adapter, concrete-runtime, cache, closure-table, and declaration-correctness contracts
clean-at-update: true
slice: Retain the structural call's budget-fit premise across the direct-call implementation boundary, construct the production-generated callee frame at the exact finite source-body cost, prove physical argument arity, and package finite callee evaluation into the cache-aware successful-declaration theorem
files: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean; integration/talos/PLAN.md; bugs/FIR-BUG-wasm-none-direct-callee-budget-premise.md; this mailbox
contracts: no semantic Wasm ABI, lowering, validator, adapter, concrete-runtime, cache, or closure-table contract changed; the proof interface DirectDeclarationCallImplementationWithCache now retains the existing stepCost <= remainingBytes fact instead of discarding it, and generatedDirectCalleeEntryAtCost, targetParameterCount, and budgetedDeclarationWithCache_of_reuseCapacityBudgetedCodeEvaluates are proof-only consequences of accepted production equations and invariants
checks: PASS Lean Beam update/sync/save FirTalos/ConcreteReuseCapacityCacheCorrectness.lean (zero errors; 7 existing warnings) and update/refresh/sync/save FirTalos/ConcreteCompilerCorrectnessContract.lean (zero errors, zero warnings); PASS lake build FirTalos.ConcreteReuseCapacityCacheCorrectness FirTalos.ConcreteCompilerCorrectnessContract (3104 jobs); PASS make bug-cards (104 active cards); PASS make talos-setup (Talos a01d01c778b794dd00956748a067b6793c2c9f9b); PASS git diff --check before and after no-op rebase; PASS make check on the exact handoff base (122 interpreter-validator tests; 642 unique validation cases; 1844/1844 comparisons equal; zero findings; bug cards and trusted assumptions valid); PASS make talos-check on the exact handoff base (3125 jobs)
bug-cards: FIR-BUG-wasm-none-direct-callee-budget-premise (fixed by this slice)
blockers: none
handoff: e05c9110cf302c9b850be5583a4dc01ae1a925f7 is the clean green W6 functional head based directly on main at dcb7d6b3; it is the first production recursive induction step, deriving the exact-cost generated callee package from finite source evaluation and uniform runtime laws without target execution or a translation certificate
next: integration owner lands this ready slice; W6 then defines a source-only hereditary finite-evaluation relation whose direct-call constructor carries the callee-body and continuation derivations, and recurses over it before adding saturated-closure and lazy-miss constructors
```
