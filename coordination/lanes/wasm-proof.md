# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 6db0646a on main
functional-head: 034b6330
contract-base: 6db0646a on main; production closure export partial correctness is linked/accepted
clean-at-update: true
slice: Generalize the one-closure-layer source boundary to a recursively hereditary production relation and preserve the certificate-free whole-export theorem
files: integration/talos/FirTalos/ConcreteCompilerCorrectness.lean; integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; this mailbox
contracts: Adds generic facts-indexed invariant transport combinators, entry-relative cache/ABI conversions, ProductionHereditaryCallSupported, a cache-aware declaration theorem, and a public export theorem; changes no shared source semantics, symbolic Wasm ABI, resident-helper signature, concrete layout, or executable artifact
checks: PASS Lean Beam update/sync/save checkpoints for both edited modules; PASS lake build FirTalos.ConcreteCompilerCorrectnessContract FirTalos.ConcreteReuseCapacitySupportedExportCorrectness (3105 jobs); PASS git diff --check; PASS make check (642 unique validation cases, 1844/1844 comparisons equal, zero findings); PASS make talos-setup at a01d01c; PASS make talos-check (3125 jobs)
bug-cards: none
blockers: none
handoff: the production closure export theorem is linked/accepted on main at 6db0646a; this lane is building recursive closure admission from that clean base
next: factor saturated closure source-step reconstruction over an arbitrary finite callee result, define the recursive production relation, and derive its exact source-result erasure
```
