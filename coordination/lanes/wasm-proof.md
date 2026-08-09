# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 38c590b0 on main
functional-head: none yet
contract-base: 38c590b0 on main; derived closure-resolver packaging and finite whole-export correctness are linked/accepted
clean-at-update: true
slice: State the first certificate-free finite-observation weak-simulation theorem for generated exports, using an explicit observation relation and internal target execution so the statement applies to every finite source prefix independently of source termination
files: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/PLAN.md; integration/talos/README.md; this mailbox
contracts: No shared semantic, ABI, concrete-layout, resident-helper, or artifact change is planned; prefer a proof-local observation/prefix layer unless inspection shows that a genuinely shared transition contract is required
checks: pending
bug-cards: none
blockers: none
handoff: not ready
next: Inventory existing source and target step/trace relations, write the exact theorem and observation boundary, then prove the strongest non-certificate finite-prefix result supported by the current execution semantics
```
