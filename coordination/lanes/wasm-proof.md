# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 0746d195 on main
functional-head: 1b0dfc7d (complete resource-indexed direct-value structured simulation spine)
contract-base: 0746d195; proof-only extension of the accepted W6.7e flat-prefix checkpoint over unchanged structured-machine and concrete-runtime contracts
clean-at-update: true
slice: Completed W6.7e's resource-indexed direct-value spine. Production compileArgs and runtime-call alignment now prove one uniform flat-target law for every ReuseBudgetedDirectSupported operation. The generic finite-path induction composes exact source let/return steps with structured Wasm paths and finishes at a value-related yielded/returning focus; the concrete endpoint instantiates the existing ConcreteReuseCapacityFrame and runtime theorem without a caller-supplied target execution or certificate.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof construction over accepted contracts
checks: lean-beam save FirTalos/ConcreteStructuredSimulation.lean (pass); lake env lean FirTalos/ConcreteStructuredSimulation.lean (pass); lake build FirTalos.ConcreteStructuredSimulation (pass, 3110 jobs); git diff --check (pass); make check (pass, 642 covered cases and 1844/1844 comparisons); make talos-setup && make talos-check (pass, 3133 jobs)
bug-cards: none
blockers: none
handoff: ready for integration; base 0746d195, functional head 1b0dfc7d, worktree clean when this mailbox update is committed
next: Lift the direct spine through the entry-relative saved-frame relation for recursive internal calls, then extend the ranked relation across external, lazy/cache, case, and effect transitions.
```
