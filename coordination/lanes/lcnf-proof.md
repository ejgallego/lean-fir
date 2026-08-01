# lcnf-proof lane

```text
lane: lcnf-proof
owner: lcnf-proof
branch: proof/simpcase
worktree: .worktrees/proof-simpcase
state: ready
base: 89fda41ae9d347aadc00bb1a6f18f7451d1e24f2
functional-head: 1640c7d47b50556d4056a9bcf96fcc6a7f5a3fba
contract-base: 89fda41ae9d347aadc00bb1a6f18f7451d1e24f2
clean-at-update: true
slice: Relate persistent, exclusive-transfer, and shared-decrement/retain closure application across AlphaEqv, SimpCase, ElimDead, reachability-aware runtime proofs, terminal faults, and external waiting-state execution
files: Fir/LeanIR/Passes/AlphaEqvCode.lean; Fir/LeanIR/Passes/SimpCaseRelation.lean; Fir/LeanIR/Passes/ElimDeadRelation.lean; Fir/LeanIR/Passes/ElimDeadProgram.lean; Fir/LeanIR/Passes/ElimDeadRuntimeRel.lean; Fir/LeanIR/Passes/ElimDeadMachineRel.lean; Fir/LeanIR/Passes/ElimDeadExamples.lean; bugs/FIR-BUG-impure-none-closure-application-external-runtime.md
contracts: consumes CLOSURE-APPLICATION-OWNERSHIP and corrected post-application external waiting-state semantics from 89fda41a; changes no shared contract
checks: Lean Beam save Fir/LeanIR/Passes/ElimDeadMachineRel.lean PASS (0 errors); Lean Beam save Fir/LeanIR/Passes/ElimDeadExamples.lean PASS (0 errors); lake build Fir.LeanIR.Passes.ElimDeadExamples PASS (34 jobs); git diff --check PASS; make check PASS (122 validator tests, 1844/1844 backend comparisons equal, bug-card validation PASS, exactly one registered trusted axiom)
bug-cards: FIR-BUG-impure-none-closure-application-external-runtime fixed with regression Fir/LeanIR/Passes/ElimDeadExamples.lean
blockers: none
handoff: integration may land branch proof/simpcase through functional-head 1640c7d47b50556d4056a9bcf96fcc6a7f5a3fba plus this ready mailbox commit
next: integration resolves the branch head, revalidates the dependency-ordered candidate stack, updates coordination/BOARD.md, and fast-forwards main
```
