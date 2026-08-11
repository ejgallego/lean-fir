# lcnf-proof lane

```text
lane: lcnf-proof
owner: lcnf-proof
branch: proof/simpcase
worktree: .worktrees/proof-simpcase
state: ready
base: d6a77d9d53d9f651ce712f8b4f84d8a532a17093 on main
functional-head: 2d31c6499100640bc93243b73468af46110cfeb2
contract-base: d6a77d9d53d9f651ce712f8b4f84d8a532a17093; consumes the accepted closure ownership, external waiting-runtime, and subsequent proof-neutral validation/artifact integrations
clean-at-update: true
slice: ELIMDEAD-GENERIC-MAPPED-OWNER-READINESS first vertical slice: an arbitrary allocated target prefix covered by compiler-live heap binders derives TargetMappedOwnerPrefix uniformly from EnvRelOn; the retained-prefix reset and reuse clients consume this interface instead of reconstructing a singleton address mapping manually
files: Fir/LeanIR/Passes/ElimDeadMachineRel.lean; Fir/LeanIR/Passes/ElimDeadExamples.lean; coordination/lanes/lcnf-proof.md
contracts: none; proof-only compiler-readiness strengthening over accepted semantics
checks: Lean Beam save Fir/LeanIR/Passes/ElimDeadMachineRel.lean PASS (0 errors, 141 warnings, source hash 0c7efce507825b21); Lean Beam save Fir/LeanIR/Passes/ElimDeadExamples.lean PASS (0 errors, 28 warnings, source hash 5d01bbab0f25d83e); lake build Fir.LeanIR.Passes.ElimDeadExamples PASS (34 jobs); git diff --check PASS; make check PASS (122 harness tests, 645/645 source native-LCNF, 9/9 direct machine, 645/645 native-LCNF-V8, 654 unique cases, 1944/1944 comparisons equal, 6184 interpreter steps, 98/98 tag floors, 209/209 semantic domains, zero findings, 129 valid bug cards, exactly one registered trusted axiom)
bug-cards: none
blockers: none
handoff: integration may land branch proof/simpcase through functional-head 2d31c6499100640bc93243b73468af46110cfeb2 plus this ready mailbox commit
next: after integration, rebase on main and replace the remaining fixture-specific RetainedPrefixReuseSourceSpecialAt reset/reuse classification with generic local operation-shape and ownership premises
```
