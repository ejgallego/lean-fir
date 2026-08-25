# lcnf-proof lane

```text
lane: lcnf-proof
owner: lcnf-proof
branch: proof/simpcase
worktree: .worktrees/proof-simpcase
state: active
base: cf3f7cb88506d9a282a444e5757b0e48acc296ee on main
functional-head: 9d34cf82229a44e34a694273f79aa740fd5b257e on main; accepted Array runtime-relation adaptation, with no lane-local repair commit yet
contract-base: cf3f7cb88506d9a282a444e5757b0e48acc296ee; consumes the accepted Lean 4.33 runtime, Array heap-object relation and ownership semantics, and subsequent proof-neutral W6/W7, validation, performance, and coordination integrations
clean-at-update: true
slice: ELIMDEAD-ARRAY-MACHINE-PROOF-RECOVERY: refresh the current main proof cone, repair thirteen missing Array branches in the ElimDead machine relation without weakening Array ownership semantics, and add a forced direct-elaboration regression before resuming generic target-prefix work
files: bugs/FIR-BUG-impure-elimDeadVars-array-machine-proof-exhaustiveness.md; coordination/lanes/lcnf-proof.md; planned repair in Fir/LeanIR/Passes/ElimDeadMachineRel.lean with importer validation through Fir/LeanIR/Passes/ElimDeadExamples.lean
contracts: none; this is a proof adaptation to the already accepted Array heap-object contract
checks: PASS rebase proof/simpcase onto exact main cf3f7cb8; the only post-audit base change is coordination/BOARD.md and the proof failure reproduces on identical Lean sources. PASS Lean Beam refresh/save Fir/LeanIR/Passes/ElimDeadRuntimeRel.lean (0 errors, 54 warnings, source hash 5d3389b60143d6a8); FAIL Lean Beam refresh Fir/LeanIR/Passes/ElimDeadMachineRel.lean (13 missing Array alternatives, 141 warnings, not save-ready); FAIL lake build +Fir.LeanIR.Passes.ElimDeadMachineRel with the same 13 errors; PASS trusted-assumption validation with exactly one registered axiom; PASS proof-hole scan; PASS make bug-cards with 196 active cards; PASS git diff --check
bug-cards: FIR-BUG-impure-elimDeadVars-array-machine-proof-exhaustiveness (candidate)
blockers: none; the repair is localized but required before any new proof handoff
handoff: none; current main cannot receive a green LCNF proof handoff until the Array repair and forced examples cone pass
next: repair and force-rebuild the thirteen Array branches; then derive the target live-prefix premise for multi-location residual/control states and remove the singleton retained-prefix adapter from the next source-plan fixture
```
