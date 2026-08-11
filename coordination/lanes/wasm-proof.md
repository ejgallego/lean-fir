# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: d6a77d9d on main
functional-head: 6ffb9528 (complete structured pure-external protocol at source-step boundaries)
contract-base: d6a77d9d; proof work over the accepted structured compiler/runtime contracts; the intervening repeated-capture fixture stack changes no W6 contract
clean-at-update: true
slice: Added the generic pure-external call shape, an exact compiled-argument path, external-call-ready and external-bind focuses, and their observation laws. The production transition is split into argument staging, imported-call execution, and destination binding with exact target path lengths |arguments|, 1, and 1. ConcreteStructuredControlRel now has nine constructors. ConcreteExternalCallEvidence isolates the runtime/resource obligation without adding a certificate premise to the public compiler theorem.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof-side staging relation and roadmap only
checks: git diff --check PASS; Lean Beam update/sync/save PASS at version 1 (0 errors, 1 pre-existing warning); forced lake env lean FirTalos/ConcreteStructuredSimulation.lean PASS before final linter cleanup; lake build FirTalos.ConcreteStructuredSimulation PASS (3110 jobs) after final rebase; make talos-check PASS (3133 jobs); make check PASS after one transient fir-native-oracle build timeout was cleared by exact rerun (645/645 source/LCNF, 9/9 direct machine, 1935/1935 native/LCNF/V8 results, findings 0; trusted-assumption audit PASS)
bug-cards: none
blockers: none
handoff: ready for integration owner to fast-forward main from d6a77d9d through the branch status commit containing functional-head 6ffb9528
next: Derive ConcreteExternalCallEvidence from the existing Int/Nat/scalar operation laws plus the concrete budget frame, then close the saturated-closure pre-entry stage and assemble the ranked simulation theorem.
```
