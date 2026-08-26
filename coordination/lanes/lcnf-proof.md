# lcnf-proof lane

```text
lane: lcnf-proof
owner: lcnf-proof
branch: proof/simpcase
worktree: .worktrees/proof-simpcase
state: ready
base: fc56e2ee6c5c8972ba85dafce544fd4fdbbd67ef on main
functional-head: 7fc463c2da854a2e6482e44705e60ee753357d18; generalizes ElimDead deleted-operation readiness from a singleton returned owner to arbitrary multi-location live heap prefixes and repairs the missed heap-only UInt64 unbox proof consumer
contract-base: fc56e2ee6c5c8972ba85dafce544fd4fdbbd67ef; consumes the accepted Lean 4.33 heap-only UInt64 contract, machine ownership relation, target allocation ledger, and ElimDead source-plan readiness surface
clean-at-update: true
slice: ELIMDEAD-ARBITRARY-LIVE-PREFIX: replaced singleton retained-prefix adapters and duplicated fixture proofs with TargetLiveHeapPrefixControlAt and DeletedLedgerLiveHeapPrefixOperationAt, supporting arbitrary target frontiers, residual code, live binders, and source owners; added a two-location non-return residual proof; freshly elaborated the heap-only UInt64 unbox ownership branch instead of relying on a stale artifact
files: Fir/LeanIR/Passes/ElimDeadMachineRel.lean; Fir/LeanIR/Passes/ElimDeadExamples.lean; bugs/FIR-BUG-impure-elimDead-machine-uint64-unbox-effect.md; coordination/lanes/lcnf-proof.md
contracts: none; proof-interface generalization only, with the UInt64 repair adapting to the already accepted heap-only representation
checks: PASS rebase proof/simpcase onto exact main fc56e2ee; PASS Lean Beam refresh/save Fir/LeanIR/Passes/ElimDeadMachineRel.lean (0 errors, 143 pre-existing warnings, source hash 1a20a6a30dc9a9b8); PASS Lean Beam refresh/save Fir/LeanIR/Passes/ElimDeadExamples.lean (0 errors, 28 pre-existing warnings, source hash ab2c8815646afdbf); PASS lake build +Fir.LeanIR.Passes.ElimDeadMachineRel +Fir.LeanIR.Passes.ElimDeadExamples (34 jobs, forced dependency cone); PASS make check on exact base fc56e2ee (21 tooling tests, 22 root jobs, 42 example jobs, 125 harness tests, 719/719 native-LCNF cases, 9/9 direct machine cases, 719/719 native-LCNF-V8 cases, 728 unique cases, 2166/2166 comparisons equal, 9097 machine steps, all 210 semantic-tag and 299 semantic-domain floors, zero findings, 204 active bug cards, 26 mailbox tests, validated Lean 4.33 source hashes and exactly one registered trusted axiom); PASS git diff --check
bug-cards: FIR-BUG-impure-elimDead-machine-uint64-unbox-effect (fixed)
blockers: none
handoff: ready; integrate functional head 7fc463c2 and this containing status commit from proof/simpcase, rebased on exact main fc56e2ee, with no shared-contract change
next: derive TargetLiveHeapPrefixControlAt automatically from arbitrary checked compiler residuals so later reset/reuse source plans do not need a client-supplied target-control invariant
```
