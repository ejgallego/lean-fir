# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: a8b127dc on main
functional-head: b8bbe5a7
contract-base: 6061b90c on main; the hereditary lazy source admission and derived hit/miss theorem build on the unchanged shared interpreter, symbolic Wasm, adapter, concrete-runtime, cache, and closure-table contracts
clean-at-update: true
slice: Localize the non-heap lazy-publication restriction in each admitted source miss, where the selected exact ABI result kind is already available; remove the separate module-wide resultKinds premise from the generated operation laws, declaration induction, named-call implementation, root declaration correctness, public export theorem, and contract example
files: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean; this mailbox
contracts: proof-only source admission and compiler-correctness theorem surface; every hereditary lazy miss now carries its exact local non-object/non-tobject publication condition, and the public theorem requires only the generated cache environment beyond source evaluation and the ordinary entry frame; no semantic Wasm ABI, lowering, validator, adapter, concrete-runtime, cache, closure-table, or interpreter contract changed
checks: PASS Lean Beam update/sync/save of ConcreteReuseCapacityCacheCorrectness (zero errors; ten pre-existing/style warnings) and refresh/save of ConcreteCompilerCorrectnessContract (zero errors); PASS focused lake build FirTalos.ConcreteReuseCapacityCacheCorrectness FirTalos.ConcreteCompilerCorrectnessContract (3104 jobs); PASS git diff --check; PASS make check (642 unique validation cases; 1844/1844 comparisons equal; zero findings; 111 bug cards and trusted assumptions valid); PASS make talos-check (3125 jobs)
bug-cards: none
blockers: none
handoff: ready for fast-forward integration; branch contains functional commit b8bbe5a7 after main and is clean at this mailbox update
next: assess fixture demand for nested lazy initializers; otherwise take the next unsupported production evaluator branch, expected to be closure application/dispatch, while preserving the same certificate-free public theorem shape
```
