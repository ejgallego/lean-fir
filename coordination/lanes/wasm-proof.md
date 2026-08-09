# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 9dab5f3c on main
functional-head: 9f6c5a05
contract-base: 9dab5f3c on main; recursive whole-export correctness, generic object-family ABI, and current Illuminate package pins are linked/accepted
clean-at-update: true
slice: Replace the overtotal dynamic closure resolver with a static candidate adapter boundary, then derive every concrete matcher return at the actual mapped live closure address from the simulation invariant and source ownership transition; apply the repair to both the older one-layer theorem and the recursive whole-export theorem
files: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; bugs/FIR-BUG-wasm-none-closure-resolver-invalid-address-totality.md; this mailbox
contracts: Removes the invalid universal store/address matcher-success premise; static resolver rows contain only symbolic candidate identity, numeric adaptation, and host-contract alignment, while W6 derives miss/hit execution dynamically from runtime refinement, immutable closure tables, shared capacity, and the semantic application; changes no shared source semantics, symbolic Wasm ABI, resident-helper signature, concrete layout, executable artifact, or W7 runtime contract
checks: PASS Lean Beam sync/save (0 errors, 17 warnings, source 3bd24b16f74f7ad5); PASS post-rebase lake build FirTalos.ConcreteReuseCapacityCacheCorrectness FirTalos.ConcreteReuseCapacitySupportedExportCorrectness (3104 jobs); PASS git diff --check; PASS post-rebase make check (642 unique validation cases, 1844/1844 comparisons equal, zero findings, 113 bug cards validated); PASS post-rebase make talos-check (3125 jobs)
bug-cards: FIR-BUG-wasm-none-closure-resolver-invalid-address-totality (fixed by 9f6c5a05; resolution f4bf542e, refreshed after rebase in this handoff)
blockers: none
handoff: ready for the integration owner to land bug-card commit 1d55e858, functional commit 9f6c5a05, resolution commit f4bf542e, followed by this containing mailbox commit from wasm/talos-runtime
next: derive the remaining static candidate-adapter environment directly from lowering/adaptation completeness, then begin the separately stated trace/coinductive extension
```
