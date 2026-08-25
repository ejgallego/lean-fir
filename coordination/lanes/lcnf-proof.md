# lcnf-proof lane

```text
lane: lcnf-proof
owner: lcnf-proof
branch: proof/simpcase
worktree: .worktrees/proof-simpcase
state: ready
base: 051a70e0ccf8289cb1262c1c39b4587b7279bd29 on main
functional-head: b8a6cb2a4a1e0343ecfea85804ae4102da64f423; repairs all thirteen Array alternatives in the ElimDead machine proof and resolves the proof-exhaustiveness bug card
contract-base: 051a70e0ccf8289cb1262c1c39b4587b7279bd29; consumes the accepted Lean 4.33 runtime, Array heap-object relation and ownership semantics, and subsequent proof-neutral W6/W7, validation, performance, package-ratchet, and coordination integrations
clean-at-update: true
slice: ELIMDEAD-ARRAY-MACHINE-PROOF-RECOVERY: repaired thirteen missing Array branches in the ElimDead machine relation without weakening Array ownership semantics, forced fresh elaboration of the machine proof and examples importer, and restored the full repository gate
files: Fir/LeanIR/Passes/ElimDeadMachineRel.lean; bugs/FIR-BUG-impure-elimDeadVars-array-machine-proof-exhaustiveness.md; coordination/lanes/lcnf-proof.md
contracts: none; this is a proof adaptation to the already accepted Array heap-object contract
checks: PASS rebase proof/simpcase onto exact main 051a70e0; PASS Lean Beam sync/save Fir/LeanIR/Passes/ElimDeadMachineRel.lean (0 errors, 141 pre-existing warnings, source hash 6ea717a2a8c37737 before the proof-neutral final rebase); PASS lake build +Fir.LeanIR.Passes.ElimDeadMachineRel (32 jobs, forced rebuild); PASS lake build +Fir.LeanIR.Passes.ElimDeadExamples (34 jobs, forced rebuild); PASS make check on exact base 051a70e0 (716/716 native-LCNF cases, 9/9 direct machine cases, 716/716 native-LCNF-V8 cases, 2157/2157 comparisons equal, zero findings, trusted-assumption validation exactly one registered axiom); PASS make bug-cards with 196 active cards; PASS git diff --check
bug-cards: FIR-BUG-impure-elimDeadVars-array-machine-proof-exhaustiveness (fixed)
blockers: none
handoff: ready; integrate the rebased proof/simpcase stack through this mailbox status commit after resolving the branch head, with no shared-contract change
next: after integration, derive the target live-prefix premise for multi-location residual/control states and remove the singleton retained-prefix adapter from the next source-plan fixture
```
