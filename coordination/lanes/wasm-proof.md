# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 85cc4c15 on main
functional-head: bff89571 (previous accepted structured caller-transport slice; no structural-body functional commit yet)
contract-base: 85cc4c15; consumes accepted W6.7d terminal adequacy and the accepted W6.7e compiler-focus, silent-ownership, return, bind-frame, generated direct-call entry, and hereditary caller-transport slices over the generated structured machine and concrete runtime refinements
clean-at-update: true
slice: Continue W6.7e with the structural callee-body simulation. Define the recursive saved-frame/suffix relation and thread the accepted entry-relative cache frame through admitted code constructors. Prove the return base and the first non-call continuation cases, then recursively nest the same relation for generated internal calls. Keep target paths constructed from compiler/runtime laws and preserve the zero-step silence rank.
files: coordination/lanes/wasm-proof.md; intended proof-owned modules under integration/talos/FirTalos/
contracts: none; this slice constructs the simulation over accepted source, structured-target, and concrete-runtime contracts
checks: not-run
bug-cards: none
blockers: none
handoff: none; active proof slice
next: State the minimal recursive saved-frame/suffix relation, prove its direct-call entry and yield-closure constructors, and align its resource indices with ReuseCapacityBudgetedCodeEvaluates.
```
