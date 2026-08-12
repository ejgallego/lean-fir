# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 4d9668a1 on main
functional-head: bf92264b (last accepted proof slice: supported generated call-stack closure)
contract-base: 4d9668a1; accepted supported generated call-stack and current Lean 4.33/Talos contracts
clean-at-update: true
slice: Assemble the first relation-wide one-source-step theorem for ConcreteStructuredSupportedGlobalOutcome. Dispatch local direct values, generated named/saturated call staging and entry, and generated return/pop while preserving the same strong global relation after a positive finite target path. Keep the statement independent of whole-program termination and future execution certificates.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof relation and roadmap only
checks: pending for active slice; previous accepted slice passed Lean Beam, direct 3119-job build, git diff --check, make check, and all 3143 Talos jobs
bug-cards: none
blockers: none
handoff: not ready; active proof slice
next: Inventory the strong outcome constructors and existing local transition laws, add the missing support-preserving staging wrappers, then prove the global dispatcher and extend its covered operation families.
```
