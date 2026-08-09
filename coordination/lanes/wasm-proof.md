# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 561988b1 on main
functional-head: 190dba61
contract-base: 6061b90c on main; the recursive effect-enabled operation laws and public partial-correctness corollary build on the unchanged shared interpreter, symbolic Wasm, adapter, concrete-runtime, cache, and closure-table contracts
clean-at-update: true
slice: Generalize reference-count ownership, delete, tag mutation, and object/erased/USize/scalar field-mutation resolver and operation laws from named exports to generated functions; instantiate their entry-relative whole-cache law for every exact internal row; derive recursive generated declarations and named calls whose callees may execute those effects together with pure externals; and expose certificate-free declaration and public export partial-correctness theorems for the resulting recursive fragment
files: integration/talos/FirTalos/ConcreteCompilerCorrectness.lean; integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean; this mailbox
contracts: proof-only receiver generalization and compiler-correctness theorem surface; operation resolvers depend on generated-function imports while export membership is used only by the final root theorem; target execution and recursive callee correctness remain derived; no semantic Wasm ABI, lowering, validator, adapter, concrete-runtime, cache, closure-table, or interpreter contract changed
checks: PASS Lean Beam update/sync/save and downstream refresh for all three edited modules (zero errors; pre-existing/style warnings only); PASS focused lake build of all three compiler-proof modules (3104 jobs); PASS git diff --check; PASS make check (642 unique validation cases; 1844/1844 comparisons equal; zero findings; 111 bug cards and trusted assumptions valid); PASS make talos-check (3125 jobs)
bug-cards: none
blockers: none
handoff: ready for fast-forward integration; branch contains one functional commit after main and is clean at this mailbox update
next: widen the production law constructor and public theorem to non-default cases, then lazy declarations and closure dispatch
```
