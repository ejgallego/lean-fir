# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 8ec10ffe on main
functional-head: 9feaaa00
contract-base: 8ec10ffe on main; existing concrete runtime, generated-declaration induction, cache-frame, closure ABI-alignment, and W7 resident-linker contracts
clean-at-update: true
slice: Thread cumulative closure-allocation persistence through pure natural/integer/scalar external results, generated declaration calls, effects, and lazy-cache steps; prove that ordinary hereditary generated-declaration correctness implies its closure-ABI strengthening; make the saturated closure-call runtime theorem consume only the ordinary induction; expose the fully derived production one-lazy closure-call law
files: integration/talos/FirTalos/ConcreteRuntime.lean; integration/talos/FirTalos/ConcreteCompilerCorrectness.lean; integration/talos/FirTalos/ConcreteReuseCapacityCallCorrectness.lean; integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean; this mailbox
contracts: Strengthens proof-side external, transport, and declaration-result packages with ClosureAllocationsPersistent; adds DirectHereditaryGeneratedDeclarationAbiInduction.ofInduction and a production saturated-closure runtime theorem derived solely from lowering, adaptation, ordinary generated-declaration induction, and executable resolver metadata; no shared source semantics, symbolic Wasm ABI, resident-helper signature, or concrete layout changed
checks: PASS Lean Beam update/sync/save checkpoints for every edited Lean module; PASS lake build FirTalos.ConcreteCompilerCorrectnessContract FirTalos.ConcreteReuseCapacitySupportedExportCorrectness (3105 jobs); after rebase onto 8ec10ffe: PASS git diff --check; PASS make check (642 unique validation cases, 1844/1844 comparisons equal, zero findings); PASS make talos-setup at a01d01c; PASS make talos-check (3125 jobs)
bug-cards: none
blockers: none
handoff: fast-forward main from 8ec10ffe to the containing wasm/talos-runtime mailbox commit; this removes the separate closure-ABI induction premise from the production saturated-closure runtime boundary
next: admit the production saturated-closure law into the root hereditary code family and derive an export-level partial-correctness theorem covering the scalar-closure fixtures
```
