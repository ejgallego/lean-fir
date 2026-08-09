# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: d8244e79 on main
functional-head: 034b6330
contract-base: d8244e79 on main; derived closure-ABI induction and production saturated-closure runtime law are linked/accepted
clean-at-update: true
slice: Combine generated named calls and exactly saturated closure applications in the production finite source relation, lift the closure ABI law through the ordinary cache frame using cumulative allocation persistence, and expose certificate-free whole-export partial correctness with exit ABI alignment
files: integration/talos/FirTalos/ConcreteCompilerCorrectness.lean; integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; this mailbox
contracts: Adds generic facts-indexed invariant transport combinators, entry-relative cache/ABI conversions, ProductionHereditaryCallSupported, a cache-aware declaration theorem, and a public export theorem; changes no shared source semantics, symbolic Wasm ABI, resident-helper signature, concrete layout, or executable artifact
checks: PASS Lean Beam update/sync/save checkpoints for both edited modules; PASS lake build FirTalos.ConcreteCompilerCorrectnessContract FirTalos.ConcreteReuseCapacitySupportedExportCorrectness (3105 jobs); PASS git diff --check; PASS make check (642 unique validation cases, 1844/1844 comparisons equal, zero findings); PASS make talos-setup at a01d01c; PASS make talos-check (3125 jobs)
bug-cards: none
blockers: none
handoff: ready for integration; branch resolves the containing mailbox status commit after functional head 034b6330
next: generalize the explicit one-closure-layer production frontier to recursively nested closure applications, then connect concrete fixture-specific source derivations to the public theorem
```
