# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 0966e35f on main
functional-head: f812e73f (current-step admission, continuation-independent core, direct-let core preservation, and return classification)
contract-base: 0966e35f; accepted compiler/runtime contracts and local step-admission boundary
clean-at-update: true
slice: Prove direct-call staging and generated entry against ConcreteStructuredCodeCoreRel. Reuse the accepted stack/resource push laws and attach callee-local admission only after the dynamic entry state is known.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof relation and roadmap only
checks: pending
bug-cards: none
blockers: none
handoff: not ready; active proof slice
next: Compose the existing direct-call stage and entry stack/resource laws into core-preservation theorems, then repeat for saturated calls and bind-return resumption.
```
