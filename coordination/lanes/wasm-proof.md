# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 745610b0 on main
functional-head: cbe31a53 (accepted recursive structured simulation for direct values, pure external results, and generated named calls)
contract-base: 745610b0; continues proof-only over the accepted W6.7e pure-external recursion and existing concrete lazy-cache runtime contracts
clean-at-update: true
slice: Extend the accepted resource-indexed structured simulation through both generated lazy-cache paths. Derive the exact hit and miss target prefixes from production compiler/adapter output, reuse the entry-relative cache runtime theorem, and resume recursive execution with the evolved cache/resource witness, empty pre-case join environment, and exact saved frames.
files: coordination/lanes/wasm-proof.md; intended proof-owned modules under integration/talos/FirTalos/
contracts: none; proof construction over accepted contracts
checks: not-run for this slice
bug-cards: none
blockers: none
handoff: none; active proof slice
next: Identify the production lazy-let compiler shape and the existing hit/miss entry-relative runtime theorem, then prove exact structured prefix flatness or the required conditional path decomposition without a target execution premise.
```
