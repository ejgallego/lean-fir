# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: c882cdc897a96df41bf231c117e015f8718cc1cc on main
functional-head: cbb0f0d11fe1103342a9d2841b194e4be7179a34
contract-base: c882cdc8 on main; consumes the accepted exact-budget generated-callee step plus the existing source interpreter, adapter, concrete-runtime, cache, closure-table, and declaration-correctness contracts
clean-at-update: true
slice: Define the source-recursive finite-evaluation boundary for direct named calls, carrying finite callee-body and caller-continuation derivations; reconstruct the real interpreter call prefix; and erase the richer derivation to the existing exact finite source result
files: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean; integration/talos/PLAN.md; this mailbox
contracts: no semantic Wasm ABI, lowering, validator, adapter, concrete-runtime, cache, closure-table, or interpreter contract changed; ReuseCapacityDirectHereditaryCodeEvaluates and its call-support payload are proof-only source derivations containing no target program, store, witness, execution, or translation certificate
checks: PASS Lean Beam update/refresh/sync/save after rebase for FirTalos/ConcreteReuseCapacityCacheCorrectness.lean (zero errors; 8 existing warnings) and FirTalos/ConcreteCompilerCorrectnessContract.lean (zero errors, zero warnings); PASS lake build FirTalos.ConcreteReuseCapacityCacheCorrectness FirTalos.ConcreteCompilerCorrectnessContract after rebase (3104 jobs); PASS make talos-setup after rebase (Talos a01d01c778b794dd00956748a067b6793c2c9f9b); PASS git diff --check before and after rebase; PASS make check after rebase (122 interpreter-validator tests; 642 unique validation cases; 1844/1844 comparisons equal; zero findings; 108 bug cards and trusted assumptions valid); PASS make talos-check after rebase (3125 jobs)
bug-cards: none
blockers: none
handoff: cbb0f0d11fe1103342a9d2841b194e4be7179a34 is the clean green W6 functional head based directly on main at c882cdc8; direct-call partial correctness now has a genuine structural recursion object whose nested callee execution is source semantics rather than an opaque module-wide theorem or target certificate
next: integration owner lands this ready slice; W6 then makes the production direct-call runtime law consume the hereditary support payload, uses the declaration-family selector plus induction hypothesis to eliminate DirectInternalCallDeclarationInduction, and only afterward adds saturated-closure and lazy-miss constructors
```
