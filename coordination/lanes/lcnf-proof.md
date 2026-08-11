# lcnf-proof lane

```text
lane: lcnf-proof
owner: lcnf-proof
branch: proof/simpcase
worktree: .worktrees/proof-simpcase
state: ready
base: 011dbdee91677e423914919638c46b9f0aa2aafd on main
functional-head: 960cfd761efbbe4795e20da1ee6e49b8e2b057a9
contract-base: 011dbdee91677e423914919638c46b9f0aa2aafd; consumes the accepted runtime contracts, Lean 4.33 migration, and subsequent proof-neutral W6/W7, validation, and coordination integrations
clean-at-update: true
slice: ELIMDEAD-GENERIC-LOCAL-LEDGER-OPERATIONS: replace the retained-prefix fixture's finite reset/reuse state classifier with reusable deleted-let operation shape, source-only ownership, and live-prefix premises; derive ledger readiness uniformly for ordinary and source-owned contracts; restore two pre-existing ledger-owner projection examples under Lean 4.33 by making id reduction explicit
files: Fir/LeanIR/Passes/ElimDeadMachineRel.lean; Fir/LeanIR/Passes/ElimDeadExamples.lean; coordination/lanes/lcnf-proof.md
contracts: none; proof-only compiler-readiness strengthening over accepted semantics
checks: PASS Lean Beam Fir/LeanIR/Passes/ElimDeadMachineRel.lean on Lean 4.33 (0 errors, 141 warnings, source hash 088ed97b5359b156); PASS Lean Beam Fir/LeanIR/Passes/ElimDeadExamples.lean on Lean 4.33 (0 errors, 28 warnings, source hash 373fe5f8586eff26); PASS lake build Fir.LeanIR.Passes.ElimDeadExamples (34 jobs); PASS git diff --check; PASS make check (root 22 jobs, examples 38 jobs, 122 harness tests, native/lcnf 653/653, direct machine 9/9, native/lcnf/v8 653/653 across all three pairs, coverage 662 unique cases and 1968/1968 equal comparisons, 132 active bug cards, validated Lean 4.33 source hashes and exactly one registered trusted axiom)
bug-cards: none
blockers: none
handoff: integration may land proof/simpcase through this ready mailbox status commit; functional slice ends at 960cfd761efbbe4795e20da1ee6e49b8e2b057a9
next: derive the target live-prefix premise for multi-location residual/control states, then remove the singleton retained-prefix adapter from the next source-plan fixture
```
