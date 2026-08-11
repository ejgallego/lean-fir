# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 59ea914f on main
functional-head: 19778649 (relation-wide pointwise source-step advance with generated call-row selection, ranked silence, and admission-free dynamic successors)
contract-base: 59ea914f; accepted pointwise code advance and current compiler/runtime contracts
clean-at-update: true
slice: Close the direct-ready, saturated-ready, and returned control outcomes under one global structured simulation relation. Reuse their exact entry/pop laws, preserve the hereditary resource stack, and expose admission-free dynamically reached code so fresh local admission remains a per-step premise rather than a recursive execution certificate.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof relation and roadmap only
checks: pending
bug-cards: none
blockers: none
handoff: not ready; active proof slice
next: Inventory the exact direct/saturated entry and caller-pop laws, then define the smallest global control-state sum that closes one-step transitions without storing future admissions.
```
