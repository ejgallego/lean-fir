# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 6db0646a on main
functional-head: a9c8ccfd
contract-base: 6db0646a on main; production closure export partial correctness is linked/accepted
clean-at-update: true
slice: Add a fully recursive production finite-evaluation relation whose named and saturated closure calls both contain recursive callee and continuation derivations; reconstruct closure source steps from arbitrary finite callee results and erase the relation to the public interpreter judgment
files: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean; this mailbox
contracts: Adds only proof-side source admission and erasure theorems; constructors contain no target program, target store, refinement witness, target execution, or translation certificate; changes no shared source semantics, symbolic Wasm ABI, resident-helper signature, concrete layout, or executable artifact
checks: PASS Lean Beam update/sync/save checkpoints for both edited modules, including stale-import recovery; PASS lake build FirTalos.ConcreteCompilerCorrectnessContract FirTalos.ConcreteReuseCapacitySupportedExportCorrectness (3105 jobs); PASS git diff --check; PASS make check (642 unique validation cases, 1844/1844 comparisons equal, zero findings); PASS make talos-check (3125 jobs)
bug-cards: none
blockers: none
handoff: ready for integration; branch resolves the containing mailbox status commit after functional head a9c8ccfd
next: prove the generated-row target induction over ReuseCapacityProductionHereditaryCodeEvaluates, discharge named and saturated closure cases from their recursive hypotheses, and expose the recursive whole-export theorem
```
