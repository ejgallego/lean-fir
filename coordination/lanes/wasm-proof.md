# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 5d4a9b3d on main
functional-head: 3a0508ae (accepted recursive pointwise structured call-stack relation)
contract-base: 5d4a9b3d; accepted pointwise control-stack and existing compiler/runtime contracts
clean-at-update: true
slice: Define the parallel resource-stack and source-only pointwise admission invariant over ConcreteStructuredStackRel. It must retain current and suspended fact maps, allocation budget, closure ABI, cache/ownership invariants, classify the applicable successful source step from compiler/program structure, and preserve admission at the successor without a whole-program evaluation or termination premise.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof relation and roadmap only
checks: pending
bug-cards: none
blockers: none
handoff: not ready; active proof slice
next: Establish the current-focus resource package and direct/saturated call push/pop preservation, then define the source-only local admission classifier and connect its first code/control families. Target-only case-label control follows before relation-wide advance assembly.
```
