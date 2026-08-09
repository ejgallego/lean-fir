# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: d5b828e3 on main
functional-head: 986b0f56
contract-base: 6061b90c on main; the generated-function lazy hit/miss laws build on the unchanged shared interpreter, symbolic Wasm, adapter, concrete-runtime, cache, and closure-table contracts
clean-at-update: true
slice: Generalize the compiler-derived lazy-cache miss, hit/miss implementation, non-heap transport, and public lazy-runtime refinement laws from named exports to arbitrary generated functions; remove the irrelevant export-name requirement throughout the lazy cone; and expose the remaining recursive initializer theorem as the next structural source-induction boundary
files: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean; this mailbox
contracts: proof-only receiver generalization and compiler-correctness theorem surface; export membership remains confined to the final root theorem, while lazy target execution still derives from generated layout/import facts and the concrete hit/miss runtime laws; no semantic Wasm ABI, lowering, validator, adapter, concrete-runtime, cache, closure-table, or interpreter contract changed
checks: PASS Lean Beam refresh/save of the contract and cache-correctness modules (zero current errors and warnings); PASS focused lake build of both modules (3104 jobs); PASS clean rebase onto main at d5b828e3; PASS git diff --check; PASS make check after rebase (642 unique validation cases; 1844/1844 comparisons equal; zero findings; 111 bug cards and trusted assumptions valid); PASS make talos-check after rebase (3125 jobs)
bug-cards: none
blockers: none
handoff: ready for fast-forward integration; branch contains one functional commit after main and is clean at this mailbox update
next: replace the recursive LazyCacheInternalHereditaryDeclarationInduction parameter with a nested lazy-miss source derivation and derive initializer correctness structurally; then admit that production lazy law into the recursive public theorem before closure dispatch
```
