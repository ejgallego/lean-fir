# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: in-progress
base: 00f5a6a4, current main after early closure proof coordination
functional-head: 2a1a5f55
contract-base: 00f5a6a4; W7's exact resident Nat.add body and all resident Natural helper signatures are consumed unchanged
clean-at-update: true
slice: The installed `sumCarryFrom` prepass now has a call-level theorem derived from successful adaptation, exact low/high accessor executions, and the actual function-entry convention. `NaturalMagnitudePartInstallation.terminatesWith_paddedLimbViewWord_of_memoryRel` supplies its read-only Natural operand boundary without a fresh allocation or writer frame. `NaturalSumCarryInstallation.terminatesWith_of_operandViews` composes both checked physical views and the shared magnitude ABI to return exactly the pure `addLimbWords` carry with unchanged store and caller tail. This removes the last abstract helper-call premise from the heap/heap checked-prefix proof.
files: Fir/Wasm/Concrete/NaturalAllocationCorrectness.lean; integration/talos/FirTalos/ConcreteResidentNat.lean; coordination/lanes/wasm-proof.md
contracts: No source semantics, semantic ABI, concrete runtime operation, helper signature, symbolic Wasm surface, emitter, ownership behavior, or layout changed. `NaturalSumCarryInstallation` and the new call/read theorems are proof-side installation/refinement boundaries only.
checks: Rebased the twelve-commit W6 stack without conflict from 63204d2e onto current main 00f5a6a4. `git diff --check main...HEAD` passed. Lean Beam update/sync/save passed with zero diagnostics for ConcreteResidentNat.lean (source hash 37f0396e87c48fb5). A forced batch build of `+FirTalos.ConcreteResidentNat` passed all 3,122 jobs. Post-rebase `make check` passed with 713 unique cases, 2,121/2,121 comparisons equal, zero findings, 193 active bug cards, and 25 mailbox tests. Post-rebase `make talos-setup` selected Talos 0e05edbc and `make talos-check` passed all 3,172 jobs.
bug-cards: none
blockers: none; the remaining public theorem boundary is explicit below
handoff: W7 may consume `NaturalSumCarryInstallation.terminatesWith_of_operandViews` together with the previously published exact Nat fallback and producer theorems at functional head 2a1a5f55. This is an in-progress proof checkpoint, not yet a claim that every checked-input representation is covered by one function-level theorem.
next: Add an installed-validator bundle and a generic constructor for the seven local writes in `CheckedNatAddPrefixExecution`. Compose those with the new installed carry theorem to construct the actual heap/heap checked prefix from `NaturalValidatorAdmission` and `NaturalObjectRel`; derive exact maximum count and result-count arithmetic. Then split the generated one-limb/multi-limb dispatch and lift the resulting fallback WP through the outer representation dispatcher and actual adapted function call. Treat immediate/heap and promoted-tag combinations as separate admission arms rather than weakening the heap theorem.
```
