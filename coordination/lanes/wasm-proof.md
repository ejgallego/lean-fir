# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 76ca1f18962166d60a714faca7e8daddbc7a6aee
functional-head: 7e15da0fff1f5f65edec91d1cbb293a0ce5c9c5f
contract-base: 76ca1f18962166d60a714faca7e8daddbc7a6aee
clean-at-update: true
slice: Derived reusable semantic ABI typing for admitted pure Integer, Nat, and scalar external results, proved destination binding preserves the semantic local-kind environment, and pinned the real compiled sumTo shape as an admitted production regression.
files: integration/talos/FirTalos/ConcreteFinalLcnfTyping.lean; integration/talos/FirTalos/ConcreteFinalLcnfTypingExamples.lean; integration/talos/FirTalos.lean; coordination/lanes/wasm-proof.md
contracts: additive source-semantic final-LCNF typing lemmas only; source/runtime semantics, existing admission judgments, ABI, concrete layout, lowering, and emitted code remain unchanged
checks: Lean Beam sync/save ConcreteFinalLcnfTyping, ConcreteFinalLcnfTypingExamples, and FirTalos umbrella green; lake build FirTalos.ConcreteFinalLcnfTyping FirTalos.ConcreteFinalLcnfTypingExamples green (3133 jobs); git diff --check green; make check green (730 unique cases, 2172/2172 comparisons); make talos-setup green at Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254; make talos-check green (3189 jobs, receipt 20aae5a846001015f9b48bc2a2e867fc1ee96feff1119512732f5153389de387)
bug-cards: none
blockers: none
handoff: Ready for integration as the first source-semantic admission slice; functional head 7e15da0fff1f5f65edec91d1cbb293a0ce5c9c5f.
next: Extend the same environment invariant through natural literals, scalar cases, direct recursion, ownership decrements, and returns, using sumTo as the running syntax shape rather than a finite-state certificate.
```
