# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: e7288dfc on main
functional-head: 36a67502
contract-base: e7288dfc; accepted silent runnable widening and current Lean 4.33/Talos contracts
clean-at-update: true
slice: Implemented staged pure external calls as the first non-erased operation family in the certificate-free runnable one-step closure. Current-node admission now selects Int/Nat/scalar response and exact cost; resource-indexed call-ready and bind core relations preserve the full facts/cache/closure scope and aligned supported stack across the individual request, import, and destination-write steps without storing a whole external execution.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean, integration/talos/PLAN.md, integration/talos/W6-THEOREM-ROADMAP.md, coordination/lanes/wasm-proof.md
contracts: none expected; proof-side intermediate relations over existing external/runtime contracts
checks: Lean Beam update/sync/save version 8 saveReady true with 0 errors and 15 existing warnings; direct lake build FirTalos.ConcreteStructuredSimulation passed (3119 jobs); git diff --check passed; make check passed (122 tests, 662 unique cases, 1968/1968 comparisons); make talos-setup pinned 0e05edbc and make talos-check passed (3143 jobs)
bug-cards: none
blockers: none
handoff: ready for integration; base e7288dfc, functional head 36a67502, no shared contracts changed
next: Integration owner fast-forwards main through the containing mailbox commit, records acceptance on the board, pushes main, then resyncs W6.
```
