# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: b3f5c5b9 on main
functional-head: e18cfcd2
contract-base: 6061b90c on main; the hereditary lazy source admission and derived hit/miss theorem build on the unchanged shared interpreter, symbolic Wasm, adapter, concrete-runtime, cache, and closure-table contracts
clean-at-update: true
slice: Add source-only hereditary lazy admission carrying the real nullary lowerer row and a finite initializer evaluation; derive exact generated nullary entry frames and parameter counts; and prove the entry-relative non-heap lazy hit/miss runtime law by selecting and proving the initializer target body from that nested source derivation, with no recursive target theorem premise
files: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; this mailbox
contracts: proof-only source-admission and compiler-correctness theorem surface; lazy misses now have a certificate-free one-layer theorem whose dynamic premise contains source evaluation only, while lowering/adaptation choose the target row and call index and the existing generated-declaration induction proves its execution; no semantic Wasm ABI, lowering, validator, adapter, concrete-runtime, cache, closure-table, or interpreter contract changed
checks: PASS Lean Beam update/sync/save of ConcreteReuseCapacityCacheCorrectness (zero errors; ten pre-existing/style warnings); PASS focused lake build through ConcreteCompilerCorrectnessContract (3104 jobs); PASS git diff --check; PASS make check (642 unique validation cases; 1844/1844 comparisons equal; zero findings; 111 bug cards and trusted assumptions valid); PASS make talos-check (3125 jobs)
bug-cards: none
blockers: none
handoff: ready for fast-forward integration; branch contains one functional commit after main and is clean at this mailbox update
next: instantiate the generated operation-law bundle and public partial-correctness theorem with this one-layer hereditary lazy family; then decide whether fixtures require deeper lazy nesting before closure dispatch
```
