# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 43a5c14e on main
functional-head: 382998c4 (accepted pointwise direct/saturated call resource push/pop composition)
contract-base: 43a5c14e; accepted pointwise control/resource call boundaries and existing compiler/runtime contracts
clean-at-update: true
slice: Define the recursive resource stack indexed by ConcreteStructuredFrameRel. It must tie each active callee scope to the exact boundary stored by its suspended caller, preserve each caller's fact map and outer entry anchor, and project the current resource invariant needed by local rules. Connect direct/saturated push and pop to this single relation, then begin the source-only pointwise admission classifier.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof relation and roadmap only
checks: pending
bug-cards: none
blockers: none
handoff: not ready; active proof slice
next: Define the dependent resource-stack constructors and root projection, then refactor the direct and saturated resource transition theorems to preserve that stack end to end.
```
