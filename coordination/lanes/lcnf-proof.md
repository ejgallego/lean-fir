# lcnf-proof lane

```text
lane: lcnf-proof
owner: lcnf-proof
branch: proof/simpcase
worktree: .worktrees/proof-simpcase
state: ready
base: d6599de83a000ebdc6e32804190e41cf79c25f36 on main
functional-head: e54f39d4062c05dacdaa7149eff882c640a4c06f
contract-base: d6599de83a000ebdc6e32804190e41cf79c25f36; consumes the accepted closure ownership and external waiting-runtime contracts plus the subsequent proof-neutral W6 protocol, validation-fixture, and external-evidence integrations
clean-at-update: true
slice: ELIMDEAD-GENERIC-MAPPED-OWNER-READINESS first vertical slice: an arbitrary allocated target prefix covered by compiler-live heap binders derives TargetMappedOwnerPrefix uniformly from EnvRelOn; the retained-prefix reset and reuse clients consume this interface instead of reconstructing a singleton address mapping manually
files: Fir/LeanIR/Passes/ElimDeadMachineRel.lean; Fir/LeanIR/Passes/ElimDeadExamples.lean; coordination/lanes/lcnf-proof.md
contracts: none; proof-only compiler-readiness strengthening over accepted semantics
checks: Lean Beam save Fir/LeanIR/Passes/ElimDeadMachineRel.lean PASS (0 errors, 141 warnings, source hash 0c7efce507825b21); Lean Beam save Fir/LeanIR/Passes/ElimDeadExamples.lean PASS (0 errors, 28 warnings, source hash 5d01bbab0f25d83e); lake build Fir.LeanIR.Passes.ElimDeadExamples PASS after rebase (34 jobs); git diff --check PASS; make check PASS after rebase (122 harness tests, 647/647 source native-LCNF, 9/9 direct machine, 647/647 native-LCNF-V8, 656 unique cases, 1950/1950 comparisons equal, 6431 interpreter steps, 106/106 tag floors, 215/215 semantic domains, zero findings, 129 valid bug cards, exactly one registered trusted axiom)
bug-cards: none
blockers: none
handoff: integration may land branch proof/simpcase through functional-head e54f39d4062c05dacdaa7149eff882c640a4c06f plus this ready mailbox commit
next: after integration, rebase on main and replace the remaining fixture-specific RetainedPrefixReuseSourceSpecialAt reset/reuse classification with generic local operation-shape and ownership premises
```
