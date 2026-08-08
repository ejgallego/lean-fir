# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 09689696b6213e287b3da4b3cff27a4f973393e3 on main
functional-head: e7993ecf2ec5e397106817958446edd26857d6c6
contract-base: 09689696 on main; consumes the existing lowering, adapter, concrete-runtime, and declaration-correctness contracts
clean-at-update: true
slice: Assemble every production-generated value-returning internal declaration row into one module-wide static family, eliminating repeated per-call compiler selection from the recursive proof boundary
files: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean; integration/talos/PLAN.md; this mailbox
contracts: no semantic Wasm ABI or concrete-runtime contract changed; ConcreteGeneratedDeclarationFamily is static compiler evidence derived once from the successful lowerSupported/adapt equations and universally returns each callee's independently computed context and exact symbolic/concrete row
checks: PASS Lean Beam update/sync/save FirTalos/ConcreteReuseCapacityCacheCorrectness.lean and FirTalos/ConcreteCompilerCorrectnessContract.lean (zero errors; existing imported warnings only); PASS lake build FirTalos.ConcreteReuseCapacityCacheCorrectness FirTalos.ConcreteCompilerCorrectnessContract (3104 jobs); PASS make talos-setup; PASS git diff --check; PASS make check (633 native/LCNF, 9 direct-machine, 601 native/LCNF/V8, 1844/1844 aggregate comparisons equal, findings 0); PASS make talos-check (3125 jobs)
bug-cards: none
blockers: none
handoff: e7993ecf2ec5e397106817958446edd26857d6c6 is the clean green W6 functional head based directly on main at 09689696; ConcreteGeneratedDeclarationFamily.ofSupportedPipeline constructs the complete module-wide static family with no target-execution or translation-certificate premise
next: integration owner lands this ready slice; W6 then proves the dynamic hereditary family by well-founded induction over admitted finite source executions, feeds it to named, saturated-closure, and lazy-miss laws, and exposes the whole-export partial-correctness theorem
```
