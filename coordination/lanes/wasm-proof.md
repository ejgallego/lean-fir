# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: c2ea914a7bd105ecb85125c4abdbbce14697fefe on main
functional-head: bf4eabdb1fcab2ab3a5206a9416b69aaf47b0544
contract-base: c2ea914a on main; consumes the existing lowering, adapter, concrete-runtime, and declaration-correctness contracts
clean-at-update: true
slice: Make production declaration local-layout alignment a theorem by construction, eliminating the caller-supplied layout/hygiene premise from the generated-declaration selector
files: Fir/Wasm/Lower.lean; integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean; integration/talos/PLAN.md; this mailbox
contracts: no semantic Wasm ABI or concrete-runtime contract changed; lowerDecl now constructs one canonical emitted parameter-plus-body-local row and uses it for symbolic lookup, while collectLocals exposes a proof-transparent partial_fixpoint core with the same public result boundary
checks: PASS Lean Beam update/sync/save Fir/Wasm/Lower.lean (zero diagnostics), FirTalos/ConcreteReuseCapacityCacheCorrectness.lean (zero errors; existing warnings only), and FirTalos/ConcreteCompilerCorrectnessContract.lean (zero diagnostics); PASS lake build Fir.Wasm.Lower; PASS lake build FirTalos.ConcreteReuseCapacityCacheCorrectness FirTalos.ConcreteCompilerCorrectnessContract (3104 jobs); PASS make talos-setup; PASS pre-rebase and post-rebase git diff --check; PASS pre-rebase and post-rebase make check (633 native/LCNF, 9 direct-machine, 601 native/LCNF/V8, 1844/1844 aggregate comparisons equal, findings 0); PASS pre-rebase and post-rebase make talos-check (3125 jobs)
bug-cards: none
blockers: none
handoff: bf4eabdb1fcab2ab3a5206a9416b69aaf47b0544 is the clean green W6 functional head based directly on main at c2ea914a; it removes the final static local-layout premise from ConcreteGeneratedDeclaration.exists_ofSupportedPipeline
next: integration owner lands this ready slice; W7 rebases wasm/generation because Fir/Wasm/Lower.lean changed, confirms its generated artifacts remain unchanged, and W6 next assembles production-generated declaration rows into the module-wide hereditary declaration family before exposing the whole-export partial-correctness theorem
```
