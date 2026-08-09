# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: ec1c015c on main
functional-head: ceb4531e
contract-base: ec1c015c on main; derived closure-resolver packaging and finite whole-export correctness are linked/accepted; intervening internal/unofficial documentation marker changes no semantic contract
clean-at-update: true
slice: Added a heterogeneous observation-aware weak-simulation framework with exact finite-path composition and ranked zero-step stuttering; specialized it to deterministic LCNF ExecSteps and W6 concrete world/event traces; proved every finite source prefix transports to a related finite target prefix without a termination premise; fixed the explicit resumable-Wasm interface required for the compiler theorem
files: integration/talos/FirTalos/Correctness/WeakSimulation.lean; integration/talos/FirTalos/ConcreteTraceSimulation.lean; integration/talos/FirTalos.lean; integration/talos/PLAN.md; integration/talos/README.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; adds proof-local framework and theorem interfaces without changing source semantics, symbolic Wasm ABI/instructions, concrete layout/runtime operations, resident helpers, or artifacts
checks: Lean Beam save FirTalos.Correctness.WeakSimulation passed with 0 errors and 1 linter warning (source a06bb4c92fece73c); Lean Beam save FirTalos.ConcreteTraceSimulation passed with 0 errors and 0 warnings (source 6b282fdc38c769d6); post-rebase lake build FirTalos.Correctness.WeakSimulation FirTalos.ConcreteTraceSimulation FirTalos passed (3127 jobs); post-rebase git diff --check passed; post-rebase make check passed (642 unique cases, 1844/1844 comparisons equal, 0 findings, 113 bug cards, trusted-assumption policy unchanged); post-rebase make talos-setup passed at Talos a01d01c778b794dd00956748a067b6793c2c9f9b; post-rebase make talos-check passed (3127 jobs)
bug-cards: none
blockers: none
handoff: Land functional-head ceb4531e plus this ready mailbox; the finite-prefix theorem is checked and does not misrepresent Talos OutOfFuel as a resumable state
next: Define the structured resumable Wasm configuration for the emitted subset, prove finite terminating adequacy with Talos Wasm.run, and then construct the compiler relation/rank from the existing W6 operation laws
```
