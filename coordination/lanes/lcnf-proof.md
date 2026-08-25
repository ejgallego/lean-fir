# lcnf-proof lane

```text
lane: lcnf-proof
owner: lcnf-proof
branch: proof/simpcase
worktree: .worktrees/proof-simpcase
state: ready
base: 5cb4ab0d05234d79b68f901adcb1d0929092c71f on main
functional-head: 7db352d6031ca63dc7b2b60db6269945474e2d79; repairs all thirteen Array alternatives in the ElimDead machine proof and resolves the proof-exhaustiveness bug card
contract-base: 5cb4ab0d05234d79b68f901adcb1d0929092c71f; consumes the accepted Lean 4.33 runtime, Array heap-object relation and ownership semantics, production release-header proof surface, and subsequent proof-neutral W7 coordination
clean-at-update: true
slice: ELIMDEAD-ARRAY-MACHINE-PROOF-RECOVERY: repaired thirteen missing Array branches in the ElimDead machine relation without weakening Array ownership semantics, forced fresh elaboration of the machine proof and examples importer, and restored the full repository gate
files: Fir/LeanIR/Passes/ElimDeadMachineRel.lean; bugs/FIR-BUG-impure-elimDeadVars-array-machine-proof-exhaustiveness.md; coordination/lanes/lcnf-proof.md
contracts: none; this is a proof adaptation to the already accepted Array heap-object contract
checks: PASS rebase proof/simpcase onto exact main 5cb4ab0d; PASS Lean Beam refresh/save Fir/LeanIR/Passes/ElimDeadMachineRel.lean (0 errors, 141 pre-existing warnings, source hash 6ea717a2a8c37737); PASS lake build +Fir.LeanIR.Passes.ElimDeadMachineRel +Fir.LeanIR.Passes.ElimDeadExamples (34 jobs, forced dependency cone); PASS make check on exact base 5cb4ab0d (22 root jobs, 42 example jobs, 125 harness tests, 716/716 native-LCNF cases, 9/9 direct machine cases, 716/716 native-LCNF-V8 cases, 725 unique cases, 2157/2157 comparisons equal, 8959 machine steps, all 208 semantic-tag and 297 semantic-domain floors, zero findings, 196 active bug cards, validated Lean 4.33 source hashes and exactly one registered trusted axiom); PASS git diff --check
bug-cards: FIR-BUG-impure-elimDeadVars-array-machine-proof-exhaustiveness (fixed)
blockers: none
handoff: ready; integrate the proof/simpcase stack rebased on exact main 5cb4ab0d through this mailbox status commit after resolving the branch head, with no shared-contract change
next: after integration, derive the target live-prefix premise for multi-location residual/control states and remove the singleton retained-prefix adapter from the next source-plan fixture
```
