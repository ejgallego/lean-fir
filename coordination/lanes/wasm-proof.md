# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 4d4e5b4c on main
functional-head: c7551259 (accepted complete structured simulation for arbitrarily nested generated named calls)
contract-base: 4d4e5b4c; continues proof-only over the accepted W6.7e recursive named-call simulation and existing concrete external-runtime contracts
clean-at-update: true
slice: Extend the accepted resource-indexed structured simulation through supported pure external-result lets. Derive the exact generated external prefix from the production compiler/adapter, reuse the concrete external-runtime refinement theorem, and resume the recursive continuation with exact observations, ABI result relation, evolved cache/resources, and unchanged saved frames.
files: coordination/lanes/wasm-proof.md; intended proof-owned modules under integration/talos/FirTalos/
contracts: none; proof construction over accepted contracts
checks: not-run for this slice
bug-cards: none
blockers: none
handoff: none; active proof slice
next: Identify the production external-let code shape and the entry-relative runtime refinement theorem, then compose them into the hereditary structured simulation without a target execution premise.
```
