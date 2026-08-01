# lcnf-proof lane

```text
lane: lcnf-proof
owner: lcnf-proof
branch: proof/simpcase
worktree: .worktrees/proof-simpcase
state: active
base: 89fda41ae9d347aadc00bb1a6f18f7451d1e24f2
functional-head: 7359bfb266c42f97249f5bf67fc87fe525c6037f
contract-base: 89fda41ae9d347aadc00bb1a6f18f7451d1e24f2
clean-at-update: true
slice: Relate persistent, exclusive-transfer, and shared-decrement/retain closure application across AlphaEqv, SimpCase, ElimDead, and reachability-aware runtime proofs
files: Fir/LeanIR/Passes/AlphaEqvCode.lean; Fir/LeanIR/Passes/SimpCaseRelation.lean; Fir/LeanIR/Passes/ElimDeadRelation.lean; Fir/LeanIR/Passes/ElimDeadProgram.lean; Fir/LeanIR/Passes/ElimDeadRuntimeRel.lean; bugs/FIR-BUG-impure-none-closure-application-external-runtime.md
contracts: consumes CLOSURE-APPLICATION-OWNERSHIP and corrected post-application external waiting-state semantics from 89fda41a
checks: prior Beam and direct dependency-cone checks passed on dbd7d934; corrected-base proof cone and root gate pending
bug-cards: FIR-BUG-impure-none-closure-application-external-runtime pending corrected-base proof validation
blockers: none; corrected shared contract is published
handoff: none
next: Finish ElimDeadMachineRel and ElimDeadExamples on the corrected base, rerun all gates, resolve the bug card, and mark ready
```
