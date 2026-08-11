# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: bc30ac44 on main
functional-head: 37f5f6bb (direct-call current-step admission, staging, entry, hereditary result ABI, and caller-core pop)
contract-base: bc30ac44; accepted direct-call pointwise core and current compiler/runtime contracts
clean-at-update: true
slice: Connect exactly saturated closure calls to the pointwise core without callee evaluation. Add state-indexed local admission, package silent/ranked staging, matcher and closure-consuming entry, and restore the caller core across generated matcher-label pop.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof relation and roadmap only
checks: pending
bug-cards: none
blockers: none
handoff: not ready; active proof slice
next: Define saturated-ready core packaging, compose the existing generated entry/resource push with the fused result ABI, expose saturated bind-pop focus, and reconstruct the caller core.
```
