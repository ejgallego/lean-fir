# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: db76e35a on main
functional-head: 56a3e15d (source-only pointwise admission, direct-let preservation, and return classification)
contract-base: db76e35a; accepted pointwise admission core and current compiler/runtime contracts
clean-at-update: true
slice: Carry source-only continuation admission through direct and saturated call entry/return. Define the admission-side suspended caller stack without adding execution evidence, connect it to the accepted resource/control push and pop laws, and reconstruct the caller's pointwise continuation relation after bind resumption.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof relation and roadmap only
checks: pending
bug-cards: none
blockers: none
handoff: not ready; active proof slice
next: Define the minimal admission stack keyed to the existing suspended resource stack; prove root, direct/saturated push, and direct/saturated pop projections without changing the accepted runtime/resource contracts.
```
