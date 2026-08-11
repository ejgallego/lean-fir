# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 7fb2c8ee on main
functional-head: c7551259 (complete structured simulation for arbitrarily nested generated named calls)
contract-base: 7fb2c8ee; proof-only extension over the accepted W6.7e direct-spine, caller-transport, call-entry, and bind-frame contracts
clean-at-update: true
slice: The resource-indexed structured simulation now handles arbitrary finite nesting of compiler-generated named calls. It enters the exact generated callee row, recursively simulates that body, transports the evolved cache/resource witness back across the caller frame, performs the checked result-local update, and resumes the generated continuation with exact source and target frame restoration. No target trace, callee execution package, or certificate is assumed.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof construction over accepted contracts
checks: Lean Beam save (pass, source hash adc1663391effd55); lake env lean FirTalos/ConcreteStructuredSimulation.lean (pass); lake build FirTalos.ConcreteStructuredSimulation (pass, 3110 jobs); git diff --check (pass); make check (pass, 642 unique covered cases and 1844/1844 comparisons); make talos-setup && make talos-check (pass, 3133 jobs)
bug-cards: none
blockers: none
handoff: ready for integration; base 7fb2c8ee, functional head c7551259, clean worktree at status update
next: Add the external-result structured prefix and extend the hereditary theorem through supported pure external results; then continue through lazy/cache, case, effect, and saturated-closure branches.
```
