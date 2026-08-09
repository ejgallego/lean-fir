# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: cdb8c4f3 on main
functional-head: cd8cd485
contract-base: cdb8c4f3 on main; recursive production source evaluation and exact generated-row target boundary are linked/accepted
clean-at-update: true
slice: State the exact compiler-derived boundary for recursive closure correctness: executable closure-candidate metadata for every generated internal declaration, the ordinary recursive generated-declaration target theorem, and its closure-ABI strengthening derived by cumulative allocation persistence
files: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; this mailbox
contracts: Adds proof-side target interfaces only; resolver metadata contains no source evaluation, target execution, store relation, or correctness certificate, and the induction premise is exactly a finite recursive source derivation plus an actual generated compiler row; changes no shared source semantics, symbolic Wasm ABI, resident-helper signature, concrete layout, or executable artifact
checks: PASS Lean Beam sync/save (0 errors, 16 warnings); PASS lake build FirTalos.ConcreteReuseCapacityCacheCorrectness (3103 jobs); PASS git diff --check; PASS make check (642 unique validation cases, 1844/1844 comparisons equal, zero findings); PASS make talos-setup (Talos a01d01c); PASS make talos-check (3125 jobs)
bug-cards: none
blockers: none
handoff: none; the proof-boundary slice is linked/accepted on main at cdb8c4f3 and W6 is constructing its structural target proof
next: prove the generated-row target induction over ReuseCapacityProductionHereditaryCodeEvaluates by extending the existing structural compiler theorem with its saturated-closure constructor, then expose the recursive whole-export theorem
```
