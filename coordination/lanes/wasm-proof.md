# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 9594e9ce on main
functional-head: 7ba707fb (previous accepted structured bind-frame slice; no call-entry functional commit yet)
contract-base: 9594e9ce; consumes accepted W6.7d terminal adequacy and the accepted W6.7e compiler-focus, silent-ownership, positive return-path, and structured bind-frame slices over the generated structured machine and concrete runtime refinements
clean-at-update: true
slice: Continue W6.7e by proving that the compiled direct-call entry sequence and the structured machine call transition establish ConcreteStructuredBindFrameFocus. Relate the source call's saved bind continuation, caller environment, and joins to the generated one-result target call frame, result-local residual, caller locals, and operand tail. Do not add target-execution evidence or translation certificates to the public relation.
files: coordination/lanes/wasm-proof.md; intended proof-owned modules under integration/talos/FirTalos/
contracts: none; this slice constructs the simulation over accepted source, structured-target, and concrete-runtime contracts
checks: not-run
bug-cards: none
blockers: none
handoff: none; active proof slice
next: Inventory the direct-call compiler equations and structured call-step laws, then state the weakest entry theorem whose conclusion is the accepted bind-frame focus.
```
