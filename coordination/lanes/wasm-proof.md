# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: in-progress
base: e367c3ce, current main after the accepted Nat shift caller fast path
functional-head: 01a3139e
contract-base: e367c3ce; W7's exact resident Nat.add body and all checked-add helper signatures are consumed unchanged
clean-at-update: true
slice: The checked heap/heap fallback now has installed vertical theorems for both result producers. `NaturalSumWriterInstallation.wp_checkedNatAddFallbackProgram_multi_of_installedAdmissions` closes the allocator/writer branch. `NaturalSumInstallation.wp_checkedNatAddFallbackProgram_one_of_installedAdmissions` closes the scalar one-limb branch from canonical operand admissions: it derives exact one-limb counts, zero carry, both overflow guards, and the Nat sum; constructs all four installed magnitude reads and local writes; and composes the adapted `naturalSum`. The one-limb caller retains only the genuine concrete `makeNatural` allocation execution and live-heap resources.
files: integration/talos/FirTalos/ConcreteResidentNat.lean; coordination/lanes/wasm-proof.md
contracts: No source semantics, semantic ABI, concrete runtime operation, helper signature, symbolic Wasm surface, emitter, ownership behavior, or layout changed. `NaturalSumInstallation`, the retained prefix scratch-validity fact, the total first-limb word projection, and the one-limb fact/composition theorems are proof-side abstractions over the existing resident functions and concrete runtime relations.
checks: Rebased the nineteen-commit W6 stack without conflict onto current main e367c3ce and finished 0 commits behind. `git diff --check` passed. Lean Beam update/sync/save passed with zero diagnostics for ConcreteResidentNat.lean (source hash ca76cb6ccf7676f8). Independent batch `lake build +FirTalos.ConcreteResidentNat` passed all 3,122 jobs. Final post-rebase `make check` passed with 721 unique cases, 2,145/2,145 comparisons equal, zero findings, 194 active bug cards, and 25 mailbox tests. Final `make talos-setup` selected Talos 0e05edbc and `make talos-check` passed all 3,172 jobs. The incoming W7 Nat-shift caller fast path caused no checked-add proof or contract regression.
bug-cards: none
blockers: none; the remaining public theorem boundary is explicit below
handoff: W7 may consume both installed checked heap/heap branch boundaries at functional head 01a3139e. The new one-limb theorem removes the previously manual magnitude executions, scalar guards, arithmetic equality, and local writes; the concrete `makeNatural` producer run remains deliberately explicit. This is an in-progress proof checkpoint, not yet one function-level theorem covering the branch split or every input representation.
next: Split on `checkedNaturalAddResultCount = 1` and compose the installed one- and multi-limb theorems into one checked heap/heap fallback theorem. Then lift that theorem through the outer representation dispatcher and actual adapted `natAddFunction` call. Treat immediate/heap and promoted-tag combinations as separate admission arms rather than weakening the canonical heap theorem.
```
