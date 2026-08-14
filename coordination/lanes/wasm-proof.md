# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: waiting
base: 8c5fc9f1 on main
functional-head: e989eeec
contract-base: 8c5fc9f1; consumes the accepted production-selection dispatch and validated external-bind boundary and changes no shared runtime or generation contract
clean-at-update: true
slice: W6 closes validated external-bind resumption. One source bind step now matches the exact one-step target local.set protocol and reconstructs ordinary validated compiler code with the source value installed in the caller environment, the destination reuse fact erased, and the unchanged runtime, witness, resource tail, ABI spine, continuation validation, and hereditary caller validation transported across the production theorem's exact frame equalities.
files: integration/talos/FirTalos/ConcreteStructuredValidation.lean; coordination/lanes/wasm-proof.md
contracts: none; proof-only closure of the existing concrete external-bind transition under the strengthened validation relation
checks: before rebase, Lean Beam update/sync/save PASS with zero errors for FirTalos/ConcreteStructuredValidation.lean; direct lake build FirTalos.ConcreteStructuredValidation FirTalos PASS (3148 jobs); git diff --check PASS; make check PASS (125 tests, 710 unique cases, 2112/2112 comparisons); make talos-check PASS (3148 jobs). Rebased conflict-free onto main 8c5fc9f1 after W7 production-selection dispatch landed; post-rebase git diff main...HEAD --check PASS; direct lake build FirTalos.ConcreteStructuredValidation FirTalos PASS (3148 jobs); make talos-check PASS (3148 jobs); post-rebase make check FAILS only in the integration-owned no-placeholder gate because W7-owned Fir/Wasm/Emit/SourceExamples.lean:222 contains the literal diagnostic word admitted. Repair requested in ROOT-W7-20260814-006.
bug-cards: none
blockers: Waiting for the W7-owned diagnostic-only repair requested in ROOT-W7-20260814-006 so current main and the post-rebase W6 handoff can satisfy make check.
handoff: Not ready until ROOT-W7-20260814-006 lands and the post-rebase make check gate is rerun. The proof commit itself is clean, rebased, and passes the complete Talos cone.
next: After the W7 gate repair lands, rebase, rerun git diff --check, make check, and make talos-check, publish the ready W6 handoff, then prove validator-to-current-step admission before assembling the universal one-step and finite-trace theorems.
```
