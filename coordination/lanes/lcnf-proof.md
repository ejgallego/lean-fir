# lcnf-proof lane

```text
lane: lcnf-proof
owner: lcnf-proof
branch: proof/simpcase
worktree: .worktrees/proof-simpcase
state: ready
base: 5d4a9b3dc1f0c539c7f2088d9f92ac85bf47c632 on main
functional-head: f9f8c41bdea9b085d0e4c12222cd2a8f07f602da
contract-base: 5d4a9b3dc1f0c539c7f2088d9f92ac85bf47c632; consumes the accepted runtime contracts plus proof-neutral W6 structured-simulation and validation-fixture integrations
clean-at-update: true
slice: ELIMDEAD-GENERIC-LOCAL-LEDGER-OPERATIONS: replace the retained-prefix fixture's finite reset/reuse state classifier with reusable deleted-let operation shape, source-only ownership, and live-prefix premises; derive ledger readiness uniformly for ordinary and source-owned contracts
files: Fir/LeanIR/Passes/ElimDeadMachineRel.lean; Fir/LeanIR/Passes/ElimDeadExamples.lean; coordination/lanes/lcnf-proof.md
contracts: none; proof-only compiler-readiness strengthening over accepted semantics
checks: PASS Lean Beam Fir/LeanIR/Passes/ElimDeadMachineRel.lean (0 errors, 141 warnings, source hash 1d33ad8e51adfa2e); PASS Lean Beam Fir/LeanIR/Passes/ElimDeadExamples.lean (0 errors, 28 warnings, source hash 013b353d52facd8d); PASS lake build Fir.LeanIR.Passes.ElimDeadExamples (34 jobs); PASS git diff --check; PASS make check (root 22 jobs, examples 38 jobs, 122 harness tests, native/lcnf 651/651, direct machine 9/9, native/lcnf/v8 651/651 across all three pairs, coverage 660 unique cases and 1962/1962 equal comparisons, 129 active bug cards, exactly one registered trusted axiom)
bug-cards: none
blockers: none
handoff: integration may land proof/simpcase through this ready mailbox status commit; functional slice ends at f9f8c41bdea9b085d0e4c12222cd2a8f07f602da
next: derive the target live-prefix premise for multi-location residual/control states, then remove the singleton retained-prefix adapter from the next source-plan fixture
```
