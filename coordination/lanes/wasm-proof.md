# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 7665c10135808a2fce3ca6a362e7982ef803ab67 on main
functional-head: f259f7f787273a6d237fbed0c5ff00c98327e39c
contract-base: 7665c101 on main; consumes the accepted generated-callee local relation plus the existing adapter, concrete-runtime, cache, closure-table, and declaration-correctness contracts
clean-at-update: true
slice: Construct the complete ConcreteReuseCapacityCacheFrame at a production-generated direct callee entry from the valid caller frame, the admitted call/declaration rows, and related physical arguments
files: integration/talos/FirTalos/ConcreteCompilerCorrectness.lean; integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean; integration/talos/PLAN.md; this mailbox
contracts: no semantic Wasm ABI, lowering, validator, adapter, concrete-runtime, cache, or closure-table contract changed; ConstructorArgumentsRelated.physicalLength and ConcreteReuseCapacityCacheFrame.generatedDirectCalleeEntry are proof-only consequences of the accepted production equations and invariant definitions
checks: PASS Lean Beam update/sync/save FirTalos/ConcreteCompilerCorrectness.lean and FirTalos/ConcreteReuseCapacityCacheCorrectness.lean plus update/refresh/sync/save FirTalos/ConcreteCompilerCorrectnessContract.lean (zero errors; existing warnings only); PASS lake build FirTalos.ConcreteCompilerCorrectness FirTalos.ConcreteReuseCapacityCacheCorrectness FirTalos.ConcreteCompilerCorrectnessContract (3104 jobs); PASS make talos-setup (Talos a01d01c778b794dd00956748a067b6793c2c9f9b); PASS git diff --check before and after rebase; PASS make check after rebase (122 interpreter-validator tests; 642 unique validation cases; 1844/1844 comparisons equal; zero findings; bug cards and trusted assumptions valid); PASS make talos-check after rebase (3125 jobs)
bug-cards: none
blockers: none
handoff: f259f7f787273a6d237fbed0c5ff00c98327e39c is the clean green W6 functional head based directly on main at 7665c101; every admitted generated direct call now receives the complete callee-entry invariant, inheriting runtime/failure/budget/external/cache/closure state and proving the new local layout plus vacuous entry reuse obligations without a separately supplied translation certificate or callee invariant
next: integration owner lands this ready slice; W6 then performs the finite-execution hereditary induction, using generatedDirectCalleeEntry at recursive calls and the existing expression/runtime refinement theorems for each source evaluation constructor
```
