# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: e2064631 on main
functional-head: 145f07cc (certificate-free structured pure-external execution and residual frame)
contract-base: e2064631; proof work over the accepted structured compiler/runtime contracts; intervening tail-ownership fixtures change no W6 contract
clean-at-update: true
slice: Derived ConcreteExternalCallEvidence internally by Int/Nat/scalar result-shape cases from the existing handler refinement laws, typed argument relation, and heap budget. The construction returns the exact evolved store, witness, physical result, and residual pure-external frame. Caller-facing progress theorems now compose the imported call and destination write, and advance_external_of_budget proves the complete three-source-step external protocol against the exact production argument prefix plus two target steps, returning to ordinary compiled code without an execution certificate premise.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof assembler and roadmap only
checks: git diff --check PASS; Lean Beam update/sync/save PASS at version 8 (0 errors, 1 pre-existing warning); lake build FirTalos.ConcreteStructuredSimulation PASS (3110 jobs) after final rebase; make talos-check PASS (3133 jobs); make check PASS (647/647 source/LCNF, 9/9 direct machine, 1941/1941 native/LCNF/V8 results, 1950/1950 indexed comparisons, findings 0; bug-card and trusted-assumption audits PASS)
bug-cards: none
blockers: none
handoff: ready for integration owner to fast-forward main from e2064631 through the branch status commit containing functional-head 145f07cc
next: Add the pre-entry saturated-closure staging focus and transition, then assemble the unified per-source-step advance law and structural rank.
```
