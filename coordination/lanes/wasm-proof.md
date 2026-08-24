# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 445e4428, current main after the accepted runtime-hotspot batch
functional-head: 4331050c
contract-base: 445e4428; W7's exact resident Nat.add body and all checked-add helper signatures are consumed unchanged
clean-at-update: true
slice: The installed public resident Nat.add function is now proved for two canonical heap Naturals. `ResidentPrimitives.wp_immediateNaturalPairDispatch_fallback` factors the exact false branch of the shared representation dispatcher from its low-bit test. `NaturalAddInstallation` ties every callee index in the adapted Nat.add body to the same checked-prefix, sum, allocator, and writer installations. `CheckedNaturalAddProducerResources` packages the real scalar-constructor or multi-limb allocation resources selected by the computed result count; it is an execution/resource premise, not trusted compiler evidence. `NaturalSumWriterInstallation.wp_natAddHeapDispatch_of_installedAdmissions` lifts the unified checked fallback through the outer immediate-pair dispatcher. Finally, `NaturalAddInstallation.terminatesWith_heap_of_admissions` proves the actual installed function call terminates with `CheckedNaturalAddPost` for the exact semantic sum, restores the caller tail, and preserves witness extension, closure-allocation persistence, live-heap refinement, resident-memory refinement, and the typed returned Wasm word.
files: integration/talos/FirTalos/ConcreteResidentPrimitives.lean; integration/talos/FirTalos/ConcreteResidentNat.lean; coordination/lanes/wasm-proof.md
contracts: No source semantics, semantic ABI, concrete runtime operation, helper signature, symbolic Wasm surface, emitter, ownership behavior, or layout changed. The new installation and producer-resource structures plus dispatcher/function theorems are proof-side abstractions over the existing concrete runtime and exact installed resident functions.
checks: Rebased cleanly onto current main 445e4428 and branch is 0 commits behind. `git diff --check main..HEAD` passed. Lean Beam speculative checks and update/sync/save passed with zero diagnostics for ConcreteResidentPrimitives.lean (source hash b9b10f2a3a7c1331) and ConcreteResidentNat.lean (source hash f44b11d87af62061). Independent `lake build +FirTalos.ConcreteResidentNat` passed all 3,123 jobs. Post-rebase `make check` passed with 724 unique cases, 2,154/2,154 comparisons equal, zero findings, 194 active bug cards, and 25 mailbox tests. `make talos-setup` selected Talos 0e05edbc and post-rebase `make talos-check` passed all 3,172 jobs.
bug-cards: none
blockers: none
handoff: Integration may land functional head 4331050c. W7 may consume `NaturalAddInstallation.terminatesWith_heap_of_admissions` as the installed public-call refinement boundary for heap/heap Nat.add, and the factored dispatcher theorem for other checked fallbacks.
next: Process operational request W7-W6-20260823-008: adapt `ConcreteClosureDispatch.instructions_compileClosureDispatch` to W7's selected declaration array and closed-ingress premise, preserving the finite-target function-admission proof. Rebase after this ready Nat.add slice lands before editing that proof-owned boundary.
```
