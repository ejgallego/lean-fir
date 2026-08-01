# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: waiting
base: 8a8d1387
functional-head: 8a8d1387
contract-base: d392e194 requested
clean-at-update: true
slice: Prove closure application and frame behavior against the concrete/Talos runtime
files: integration/talos/FirTalos/ and W6-owned Fir/Wasm/Concrete/ files as required
contracts: consume CLOSURE-APPLICATION-OWNERSHIP without weakening or duplicating it
checks: not-run for this milestone
bug-cards: none currently
blockers: integration must publish the stable contract-base commit on the milestone branch
handoff: none
next: Rebase from the published contract base, adapt FirTalos.Correctness.Semantics, prove the concrete refinement, and report exact Talos checks
```
