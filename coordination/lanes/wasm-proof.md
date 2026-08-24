# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: in-progress
base: c0f464bd, current main after scratch-free constructor integration and early-closure coordination
functional-head: 67b4978f
contract-base: c0f464bd; W7's exact resident Nat.add body and all resident Natural helper signatures are consumed unchanged
clean-at-update: true
slice: The heap/heap checked Nat.add prefix is now constructed from installed code and canonical operand admissions rather than assumed helper traces. `NaturalValidatorInstallation` and `NaturalAddPrefixInstallation` bundle the exact generated validator, magnitude, and carry helpers. Their composition proves both validations, exact magnitude counts, both canonical limb views, the pure final carry, all seven Wasm local writes, and the modular result-count equation. `CheckedNatAddPrefixExecution.exists_of_runs` isolates administrative local bookkeeping from helper semantics, keeping the next writer proof independent of the generated local layout.
files: integration/talos/FirTalos/ConcreteResidentNat.lean; coordination/lanes/wasm-proof.md
contracts: No source semantics, semantic ABI, concrete runtime operation, helper signature, symbolic Wasm surface, emitter, ownership behavior, or layout changed. The new installation records and execution theorems are proof-side composition boundaries over the existing resident functions.
checks: Rebased the fourteen-commit W6 stack without conflict from 00f5a6a4 onto current main c0f464bd. `git diff --check` passed. Lean Beam update/sync/save passed with zero diagnostics before checkpoint; post-rebase direct `lake env lean FirTalos/ConcreteResidentNat.lean` passed with zero diagnostics. The pre-rebase forced `+FirTalos.ConcreteResidentNat` build passed all 3,122 jobs. Post-rebase `make check` passed with 717 unique cases, 2,133/2,133 comparisons equal, zero findings, 194 active bug cards, and 25 mailbox tests. Post-rebase `make talos-setup` selected Talos 0e05edbc and `make talos-check` passed all 3,172 jobs.
bug-cards: none
blockers: none; the remaining public theorem boundary is explicit below
handoff: W7 may consume `NaturalAddPrefixInstallation.exists_checkedExecution_of_admissions` at functional head 67b4978f as the proved heap/heap admission-to-prefix boundary. This is an in-progress proof checkpoint, not yet a claim that every checked-input representation is covered by one function-level theorem.
next: Compose the constructed prefix with `NaturalSumWriterInstallation.wp_checkedNatAddFallbackProgram_multi_of_admissions`. Discharge its count, exact-count, carry, and result-count premises from the execution object, leaving only allocator/frontier/heap bounds and the generated multi-limb branch guard. Then prove the one-limb branch and lift both through the outer representation dispatcher and actual adapted `natAddFunction` call. Treat immediate/heap and promoted-tag combinations as separate admission arms rather than weakening the heap theorem.
```
