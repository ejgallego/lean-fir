# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 14242c49 on integration/hitscene-admission
functional-head: a5ab062c
contract-base: c93bf226; consumes the shared effective-declaration-result lowering contract and its 14242c49 diagnostic successor without changing the compiler candidate, AbiKind.refines, closure capture compatibility, or concrete layouts
clean-at-update: true
slice: Adapted the W6 exact lazy-cache and recursive generated-declaration proof cone to distinguish a source-declared result kind from the effective target/physical cache kind. Compiler inversion recovers the effective kind; hit and miss simulation, cache-table selection/publication, local/result lowering, and saturated closure recursion retain exact physical decoding. Removed an unused result-classification premise from generated-declaration induction and converted the former rejection witness into a successful exact-object cache regression.
files: integration/talos/FirTalos/ConcreteCacheCorrectness.lean; integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean; bugs/FIR-BUG-wasm-none-lazy-cache-result-refinement.md; coordination/lanes/wasm-proof.md
contracts: consumed effectiveDeclarationResultKind? at cached nullary calls, emitted declaration results, and saturated closure candidates; source annotations remain admitted by refinement while cacheSet/global lanes and callee results use the exact effective kind; recursive generated-declaration induction no longer requires the unused equality between the source ABI classifier and its semantic result index
checks: Lean Beam update/refresh reported no source diagnostics for ConcreteCacheCorrectness, ConcreteReuseCapacityCacheCorrectness, and ConcreteCompilerCorrectnessContract; Lean Beam saved ConcreteCacheCorrectness (source hash 6f12a25554cf0f5f), while the large downstream save barrier remained incomplete on a stale imported target; direct lake build FirTalos.ConcreteCacheCorrectness FirTalos.ConcreteReuseCapacityCacheCorrectness passed; direct lake build FirTalos.ConcreteCompilerCorrectnessContract passed; git diff --check passed; make check passed; make talos-setup passed at Talos a01d01c; final make talos-check passed all 3131 jobs
bug-cards: FIR-BUG-wasm-none-lazy-cache-result-refinement fixed; FIR-BUG-wasm-none-endpoint-partial-application-admission unchanged
blockers: none
handoff: Rebase/land the shared c93bf226/14242c49 HitScene compiler candidate followed by W6 functional head a5ab062c and this ready mailbox; the W6 worktree is clean at update and the combined proof/contract cone is green
next: After the combined stack lands, rebase wasm/talos-runtime on main and resume W6.7d structured terminal adequacy; W7 and test fixtures are unblocked on the exact effective-result cache/closure boundary
```
