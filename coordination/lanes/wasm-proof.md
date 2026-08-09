# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: aaf0cb77 on main
functional-head: d3cbae29
contract-base: 6061b90c on main; the recursive production-case operation laws and widened public partial-correctness corollary build on the unchanged shared interpreter, symbolic Wasm, adapter, concrete-runtime, cache, and closure-table contracts
clean-at-update: true
slice: Generalize object-constructor and scalar-UInt8 case-chain/runtime laws from named exports to generated functions; add disjunctive case-law composition and one ProductionCasesSupported family admitting default-only, arbitrary normalized object-constructor, and scalar-UInt8 cases in the same recursive program; and widen the generated-declaration induction, named-call implementation, declaration theorem, and public partial-correctness theorem to that family
files: integration/talos/FirTalos/ConcreteCompilerCorrectness.lean; integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean; this mailbox
contracts: proof-only source-admission composition, receiver generalization, and compiler-correctness theorem surface; case proofs depend on generated-function layout/import facts while export membership remains confined to the final root theorem; target execution and recursive callee correctness remain derived; no semantic Wasm ABI, lowering, validator, adapter, concrete-runtime, cache, closure-table, or interpreter contract changed
checks: PASS Lean Beam update/sync/save and downstream refresh for all three edited modules (zero errors; pre-existing/style warnings only); PASS focused lake build of all three compiler-proof modules (3104 jobs); PASS git diff --check; PASS make check (642 unique validation cases; 1844/1844 comparisons equal; zero findings; 111 bug cards and trusted assumptions valid); PASS make talos-check (3125 jobs)
bug-cards: none
blockers: none
handoff: ready for fast-forward integration; branch contains one functional commit after main and is clean at this mailbox update
next: widen the production law constructor and public theorem to lazy declarations, then closure dispatch
```
