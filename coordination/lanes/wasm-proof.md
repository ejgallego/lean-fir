# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 8a8d1387
functional-head: 8a8d1387
contract-base: dbd7d934 published on integration/closure-ownership
clean-at-update: true
slice: Prove closure application and frame behavior against the concrete/Talos runtime
files: integration/talos/FirTalos/ and W6-owned Fir/Wasm/Concrete/ files as required
contracts: consume CLOSURE-APPLICATION-OWNERSHIP without weakening or duplicating it
checks: not-run for this milestone
bug-cards: none currently
blockers: none; stable contract base is published
handoff: none
next: Rebase onto dbd7d934, adapt FirTalos.Correctness.Semantics, prove the concrete refinement, update this mailbox, and report exact Talos checks
```
