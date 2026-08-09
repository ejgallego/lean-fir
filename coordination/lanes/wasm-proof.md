# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 76fecb0c on main
functional-head: 1f483a13
contract-base: 6061b90c on main; the hereditary lazy source admission and derived hit/miss theorem build on the unchanged shared interpreter, symbolic Wasm, adapter, concrete-runtime, cache, and closure-table contracts
clean-at-update: true
slice: Thread the certificate-free one-layer lazy hit/miss law through uniform generated operation laws, hereditary declaration induction, recursive named-call implementation, budgeted root declaration correctness, and the public export partial-correctness theorem; coherent declaration contexts transport the validated cache environment, cache-miss initializers are proved from their nested finite source derivations, and the contract module exposes the resulting proof boundary
files: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean; this mailbox
contracts: proof-only compiler-correctness theorem surface; the public production theorem now admits real lazy-cache hits and misses and concludes source evaluation plus generated Wasm export termination/refinement without target-run or recursive-callee certificates; it additionally requires the generated cache environment and a source-only non-heap result-kind policy for coherent declaration contexts; no semantic Wasm ABI, lowering, validator, adapter, concrete-runtime, cache, closure-table, or interpreter contract changed
checks: PASS Lean Beam update/sync/save of ConcreteReuseCapacityCacheCorrectness (zero errors; ten pre-existing/style warnings) and refresh/save of ConcreteCompilerCorrectnessContract (zero errors); PASS focused lake build FirTalos.ConcreteReuseCapacityCacheCorrectness FirTalos.ConcreteCompilerCorrectnessContract (3104 jobs); PASS git diff --check; PASS make check (642 unique validation cases; 1844/1844 comparisons equal; zero findings; 111 bug cards and trusted assumptions valid); PASS make talos-setup; PASS make talos-check (3125 jobs)
bug-cards: none
blockers: none
handoff: ready for fast-forward integration; branch contains functional commit 1f483a13 after main and is clean at this mailbox update
next: move the non-heap result-kind restriction into the source lazy admission so the public theorem no longer needs a separate module-wide resultKinds premise; then assess fixture demand for nested lazy initializers before closure dispatch
```
