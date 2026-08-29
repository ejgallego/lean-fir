# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 76ca1f18962166d60a714faca7e8daddbc7a6aee
functional-head: 76ca1f18962166d60a714faca7e8daddbc7a6aee
contract-base: 76ca1f18962166d60a714faca7e8daddbc7a6aee
clean-at-update: true
slice: Use the real compiled sumTo shape to derive reusable semantic ABI typing for admitted pure Integer, Nat, and scalar external results and their destination environment binding.
files: integration/talos/FirTalos/ConcreteFinalLcnfTyping.lean; integration/talos/FirTalos.lean; coordination/lanes/wasm-proof.md
contracts: additive source-semantic final-LCNF typing lemmas only; source/runtime semantics, existing admission judgments, ABI, concrete layout, lowering, and emitted code remain unchanged
checks: not-run
bug-cards: none
blockers: none
handoff: none
next: Prove pure external result typing generically, then retain sumTo only as a compiler-shape regression before extending typing through cases, direct recursion, and returns.
```
