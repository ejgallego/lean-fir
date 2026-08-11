# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 230d805a on main
functional-head: ab58cd2e
contract-base: 230d805a; consumes accepted W6.7d terminal adequacy, the accepted W6.7e compiler-focus/silence spine, generated structured machine, concrete runtime refinements, and current W7 resident-runtime stack
clean-at-update: true
slice: W6.7e first positive structured target path. ConcreteStructuredYieldFocus relates yielded source control to explicit target return control, preserves the concrete state relation and observation agreement, and records the exact ABI-indexed PhysicalValueRel for the returned word. advance_return inverts the real two-stage compiler, resolves the generated result local, and proves one source return step is matched by exactly two structured target steps (local.get, ret). advance_return_of_step recovers the source lookup and result from the generic simulation's successful source-step premise, so no execution certificate or lookup is added to the public compiler relation.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; this slice constructs the simulation over accepted source, structured-target, and concrete-runtime contracts
checks: Lean Beam update/sync/save (version 7, 0 errors, 0 warnings); lake build FirTalos.ConcreteStructuredSimulation FirTalos.ConcreteResumableWasm (3,107 jobs); git diff --check; no sorry/admit; make check (642 unique cases, 1,844/1,844 comparisons, 124 bug cards, trusted assumptions green); make talos-setup (Talos a01d01c); make talos-check (3,133 jobs)
bug-cards: none
blockers: none
handoff: ready for fast-forward integration by the wasm-proof integration owner
next: Define source/target continuation-frame correspondence and lift yielded/returning control through bind/apply/cache and call/label/loop unwinding, so local return simulation restores the global compiler relation.
```
