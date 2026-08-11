# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: db76e35a on main
functional-head: f812e73f (current-step admission, continuation-independent core, direct-let core preservation, and return classification)
contract-base: db76e35a; accepted compiler/runtime contracts and corrected pointwise boundary
clean-at-update: true
slice: Localize source admission to the current code node and its exact one-step allocation requirement. Separate the compiler/resource/result-ABI core from local admission, expose its observation and stack projections, make direct lets preserve the successor core, and document why continuation admission or a future allocation reserve would be a disguised execution certificate.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof relation and roadmap only
checks: Lean Beam update/sync 0 errors and 1 pre-existing warning; Lean Beam save; lake build FirTalos.ConcreteStructuredSimulation (success); git diff --check (success); make check (success, 122 interpreter tests); make talos-setup (Talos a01d01c778b794dd00956748a067b6793c2c9f9b); make talos-check (success, 3133 jobs); post-check git rebase main (already current)
bug-cards: none
blockers: none
handoff: ready for integration; worktree clean at functional head before this mailbox-only status commit
next: Prove direct and saturated call staging, entry, and return against ConcreteStructuredCodeCoreRel. Attach fresh local step admission only after the dynamic successor is known; do not introduce an admission stack or future-execution reserve.
```
