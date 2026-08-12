# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: e7288dfc on main
functional-head: 0a7f8866
contract-base: e7288dfc; accepted silent runnable widening and current Lean 4.33/Talos contracts
clean-at-update: true
slice: Add staged pure external calls as the first non-erased operation family in the certificate-free runnable one-step closure. Introduce resource-indexed call-ready and bind core relations for the source protocol's individual steps, preserve the aligned supported stack through exact frame equalities, and connect current-node admission to the existing budget-derived concrete external refinement without storing a whole external execution.
files: coordination/lanes/wasm-proof.md now; expected integration/talos/FirTalos/ConcreteStructuredSimulation.lean and W6 roadmap documents
contracts: none expected; proof-side intermediate relations over existing external/runtime contracts
checks: pending
bug-cards: none
blockers: none
handoff: not ready; active W6 proof slice
next: Inventory exact external focus laws and resource indices, then define the two intermediate core relations and their one-source-step closures.
```
