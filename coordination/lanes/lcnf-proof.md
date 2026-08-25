# lcnf-proof lane

```text
lane: lcnf-proof
owner: lcnf-proof
branch: proof/simpcase
worktree: .worktrees/proof-simpcase
state: ready
base: ec734c92d4808d810238a8acb1a80d1acf7e3676 on main
functional-head: 76f099fdc6911880e5dd25a60ac80b31608e6cc4; repairs all thirteen Array alternatives in the ElimDead machine proof and resolves the proof-exhaustiveness bug card
contract-base: ec734c92d4808d810238a8acb1a80d1acf7e3676; consumes the accepted Lean 4.33 runtime, Array heap-object relation and ownership semantics, production release-header proof surface, and subsequent proof-neutral W7 coordination and S20 fixture integration
clean-at-update: true
slice: ELIMDEAD-ARRAY-MACHINE-PROOF-RECOVERY: repaired thirteen missing Array branches in the ElimDead machine relation without weakening Array ownership semantics, forced fresh elaboration of the machine proof and examples importer, and restored the full repository gate
files: Fir/LeanIR/Passes/ElimDeadMachineRel.lean; bugs/FIR-BUG-impure-elimDeadVars-array-machine-proof-exhaustiveness.md; coordination/lanes/lcnf-proof.md
contracts: none; this is a proof adaptation to the already accepted Array heap-object contract
checks: PASS rebase proof/simpcase onto exact main ec734c92; PASS Lean Beam refresh/save Fir/LeanIR/Passes/ElimDeadMachineRel.lean (0 errors, 141 pre-existing warnings, source hash 6ea717a2a8c37737); PASS lake build +Fir.LeanIR.Passes.ElimDeadMachineRel +Fir.LeanIR.Passes.ElimDeadExamples (34 jobs, forced dependency cone); PASS make check on exact base ec734c92 (21 tooling tests, 22 root jobs, 42 example jobs, 125 harness tests, 717/717 native-LCNF cases, 9/9 direct machine cases, 717/717 native-LCNF-V8 cases, 726 unique cases, 2160/2160 comparisons equal, 9077 machine steps, all 210 semantic-tag and 299 semantic-domain floors, zero findings, 196 active bug cards, validated Lean 4.33 source hashes and exactly one registered trusted axiom); PASS git diff --check main...HEAD
bug-cards: FIR-BUG-impure-elimDeadVars-array-machine-proof-exhaustiveness (fixed)
blockers: none
handoff: ready; integrate the proof/simpcase stack rebased on exact main ec734c92 through this mailbox status commit after resolving the branch head, with no shared-contract change
next: after integration, derive the target live-prefix premise for multi-location residual/control states and remove the singleton retained-prefix adapter from the next source-plan fixture
```
