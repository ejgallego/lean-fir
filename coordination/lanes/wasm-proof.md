# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 05ebaab1 on main
functional-head: 6ffb9528 (complete structured pure-external protocol; integrated on main)
contract-base: 05ebaab1; proof work over the accepted structured compiler/runtime contracts
clean-at-update: false
slice: Reopened to derive ConcreteExternalCallEvidence uniformly from the existing concrete Int, Nat, and scalar operation laws plus ConcreteBudgetedPureExternalFrame. The public compiler theorem must obtain this evidence internally; no execution certificate will be exposed to callers.
files: coordination/lanes/wasm-proof.md; planned integration/talos/FirTalos/ConcreteStructuredSimulation.lean and W6 roadmap documents
contracts: none planned; proof assembler over existing runtime contracts
checks: not-run
bug-cards: none
blockers: none
handoff: none
next: Prove the evidence assembler by result-shape cases, use it to remove the explicit evidence parameter from external-call progress, then resume saturated-closure pre-entry.
```
