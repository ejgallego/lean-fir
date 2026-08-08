# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: d69e0252d7380b972d0cdd30bde4d502265414eb on main
functional-head: a83651c4f6f9f4ce23e71b17476fba6f68918665
contract-base: d69e0252 on main; consumes the existing lowering, adapter, concrete-runtime, declaration-correctness, and generated-declaration-family contracts
clean-at-update: true
slice: Retain each production-generated internal declaration's exact addDeclarationParams row and emitted parameter identity, together with the direct-call validator's argument/result refinement facts, so recursive proofs can construct the callee-entry relation
files: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean; integration/talos/PLAN.md; this mailbox
contracts: no semantic Wasm ABI or concrete-runtime contract changed; ConcreteGeneratedDeclarationFamily now returns the stronger static ConcreteGeneratedInternalDeclaration row, while DirectInternalCallSite retains the existing production support equations without changing their definitions
checks: PASS Lean Beam update/sync/save FirTalos/ConcreteReuseCapacityCacheCorrectness.lean and FirTalos/ConcreteCompilerCorrectnessContract.lean (zero errors; existing imported warnings only); PASS lake build FirTalos.ConcreteReuseCapacityCacheCorrectness FirTalos.ConcreteCompilerCorrectnessContract (3104 jobs); PASS make talos-setup; PASS git diff --check; PASS make check (633 native/LCNF, 9 direct-machine, 601 native/LCNF/V8, 1844/1844 aggregate comparisons equal, findings 0); PASS make talos-check (3125 jobs)
bug-cards: none
blockers: none
handoff: a83651c4f6f9f4ce23e71b17476fba6f68918665 is the clean green W6 functional head based directly on main at d69e0252; the selected generated row now contains the production parameter data needed to initialize recursive callee frames, with no target-execution or translation-certificate premise
next: integration owner lands this ready slice; W6 then derives argument-to-parameter ABI refinement, constructs the empty-entry reuse/cache frame, and begins the well-founded dynamic hereditary proof over admitted finite source executions
```
