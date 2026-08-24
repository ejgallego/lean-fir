# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: in-progress
base: 9f53aca1, current main after closure-integration coordination refresh
functional-head: a62f83d9
contract-base: 9f53aca1; W7's exact resident Nat.add body and all resident Natural helper signatures are consumed unchanged
clean-at-update: true
slice: `checkedNaturalAddCount`, `checkedNaturalAddCarry`, and `checkedNaturalAddResultCount` expose the pure checked heap/heap arithmetic selected by the generated prefix. `NaturalSumWriterInstallation.wp_checkedNatAddFallbackProgram_multi_of_installedAdmissions` now constructs the installed prefix and composes it with the exact allocator/writer theorem through the complete multi-limb fallback. Validator calls, magnitude-count calls, carry execution, seven local writes, and the count/carry/result-count bridge equalities are internal. Callers retain only the semantic multi-limb branch guard plus genuine allocation bounds, allocator relation, and live-heap resources.
files: integration/talos/FirTalos/ConcreteResidentNat.lean; coordination/lanes/wasm-proof.md
contracts: No source semantics, semantic ABI, concrete runtime operation, helper signature, symbolic Wasm surface, emitter, ownership behavior, or layout changed. The pure projections and installed composition theorem are proof-side abstractions over the existing resident functions and concrete runtime relations.
checks: Rebased the sixteen-commit W6 stack without conflict onto current main 9f53aca1 and finished 0 commits behind. `git diff --check` passed. Lean Beam update/sync/save passed with zero diagnostics for ConcreteResidentNat.lean (source hash e9bd1861a1e6d7fe). An independent batch `lake build +FirTalos.ConcreteResidentNat` passed all 3,122 jobs. Final post-rebase `make check` passed with 721 unique cases, 2,145/2,145 comparisons equal, zero findings, 194 active bug cards, and 25 mailbox tests. Final `make talos-setup` selected Talos 0e05edbc and `make talos-check` passed all 3,172 jobs.
bug-cards: none
blockers: none; the remaining public theorem boundary is explicit below
handoff: W7 may consume `NaturalSumWriterInstallation.wp_checkedNatAddFallbackProgram_multi_of_installedAdmissions` at functional head a62f83d9 as the proved canonical heap/heap multi-limb fallback boundary. This is an in-progress proof checkpoint, not yet a claim that the one-limb branch or every checked-input representation is covered by one function-level theorem.
next: Package the installed low/high magnitude helpers and concrete `naturalSum` result relation for the one-limb producer, then construct its local writes from the same prefix execution. Split on `checkedNaturalAddResultCount = 1`, compose the one- and multi-limb branches into one checked heap/heap fallback theorem, and lift that theorem through the outer representation dispatcher and actual adapted `natAddFunction` call. Treat immediate/heap and promoted-tag combinations as separate admission arms rather than weakening the heap theorem.
```
