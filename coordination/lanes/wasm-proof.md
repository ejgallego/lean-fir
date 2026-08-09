# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 871619fb26983c7644cbcf2f49ca18a46d27ece5 on main
functional-head: cba73898e50ee733162aacd012115686c8e922ef
contract-base: 6061b90c on main; the production operation laws, generated-declaration induction, and public partial-correctness corollary build on the unchanged shared interpreter, symbolic Wasm, adapter, concrete-runtime, cache, and closure-table contracts
clean-at-update: true
slice: Derive recursive generated declarations from the real lowering rows; retain their source-program, cache-table, parameter, call-index, and local-layout facts; separate reusable generated-function support from named export membership; instantiate the hereditary operation laws from individual compiler/runtime theorems; derive recursive named-call correctness structurally; and expose a public finite-evaluation partial-correctness theorem for the reuse-budgeted direct fragment with no target-execution or recursive-callee certificate premise
files: integration/talos/FirTalos/ConcreteSupportedExportCorrectness.lean; integration/talos/FirTalos/ConcreteCompilerCorrectness.lean; integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean; bugs/FIR-BUG-wasm-none-generated-row-context-coherence.md; bugs/FIR-BUG-wasm-none-operation-laws-require-export.md; this mailbox
contracts: proof-only generated-function support and compiler-correctness theorem surface; ConcreteSupportedFunction carries reusable pipeline facts and ConcreteSupportedExport adds only export membership; recursive callees and exact target execution are derived from compiler rows and operation laws; no semantic Wasm ABI, lowering, validator, adapter, concrete-runtime, cache, closure-table, or interpreter contract changed
checks: PASS Lean Beam update/sync/save for both edited proof modules and refresh/save for the contract module (zero errors; pre-existing/style warnings only); PASS focused lake builds through FirTalos.ConcreteReuseCapacityCacheCorrectness and FirTalos.ConcreteCompilerCorrectnessContract (3104 jobs); PASS git diff --check; PASS make check (642 unique validation cases; 1844/1844 comparisons equal; zero findings; 111 bug cards and trusted assumptions valid); PASS make talos-setup (Talos a01d01c778b794dd00956748a067b6793c2c9f9b); PASS make talos-check (3125 jobs)
bug-cards: FIR-BUG-wasm-none-generated-row-context-coherence (fixed); FIR-BUG-wasm-none-operation-laws-require-export (fixed)
blockers: none
handoff: ready for fast-forward integration; branch contains four commits after main and is clean at this mailbox update
next: widen the production law constructor and public theorem beyond the no-call fragment, starting with pure external calls, then effects, non-default cases, lazy declarations, and closure dispatch
```
