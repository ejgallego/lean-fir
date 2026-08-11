# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 260ce30a on main
functional-head: 1f57b48d (accepted hereditary pointwise resource stack with direct/saturated push and pop)
contract-base: 260ce30a; accepted pointwise control/resource stack and existing compiler/runtime contracts
clean-at-update: true
slice: Define the source-only pointwise admission classifier over the combined control/resource relation. Admission must be a local property of the current compiler-produced control/code, static generated-function rows, and resource facts—not an evaluation derivation. Connect the first code/control successor families and show each successful admitted source step constructs a finite target path, successor control/resource relation, and rank decrease when the target path is empty.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof relation and roadmap only
checks: pending
bug-cards: none
blockers: none
handoff: not ready; active proof slice
next: Inventory the existing source-only admitted code predicates and operation-family progression theorems, define the minimal local admission judgment for ordinary code, and prove its root construction and first successor-preservation cases.
```
