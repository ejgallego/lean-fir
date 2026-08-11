# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 41cd4b29 on main
functional-head: 1bc6eb40 (module-stable global outcome and certificate-free generated call-entry closure)
contract-base: 41cd4b29; accepted global call entry and current compiler/runtime contracts
clean-at-update: true
slice: Retain each suspended caller's static supported-function identity and canonical cache table in a hereditary stack aligned with the existing source/target call frames. Use it with the established direct and saturated pop laws to restore the caller as ConcreteStructuredGlobalOutcome after one ordinary source step.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof relation and roadmap only
checks: pending
bug-cards: none
blockers: none
handoff: not ready; active proof slice
next: Define the static supported-frame stack, push it at named/saturated entry, and invert it together with returned resource/control frames to recover the exact caller spec and cache table.
```
