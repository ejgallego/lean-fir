# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 298682a766d80e90053d3e76ee2f3e4af78a52aa on main
functional-head: 73492cd973aa91dd25aea667b8c6141c494c908f
contract-base: 298682a7 on main; consumes the existing lowering, validator, adapter, concrete-runtime, declaration-correctness, and generated-declaration-family contracts
clean-at-update: true
slice: Transport a concrete/source argument relation across the production validator's pointwise ABI-refinement decision and retain the production-validated declaration-parameter uniqueness fact on every selected generated internal row
files: integration/talos/FirTalos/ConcreteCompilerCorrectness.lean; integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean; integration/talos/PLAN.md; this mailbox
contracts: no semantic Wasm ABI, lowering, validator, or concrete-runtime contract changed; ConstructorArgumentsRelated.ofKindsRefine is a proof-only transport theorem, and ConcreteGeneratedInternalDeclaration now retains a theorem derived from the existing declarationParameterIdsUnique validation decision
checks: PASS Lean Beam update/sync/save FirTalos/ConcreteCompilerCorrectness.lean and FirTalos/ConcreteReuseCapacityCacheCorrectness.lean, then refresh/save FirTalos/ConcreteCompilerCorrectnessContract.lean after the rebase (zero errors; existing warnings only); PASS lake build FirTalos.ConcreteCompilerCorrectness FirTalos.ConcreteReuseCapacityCacheCorrectness FirTalos.ConcreteCompilerCorrectnessContract (3104 jobs); PASS make talos-setup (Talos a01d01c778b794dd00956748a067b6793c2c9f9b); PASS git diff --check; PASS make check (122 interpreter-validator tests plus repository validation plans); PASS make talos-check (3125 jobs)
bug-cards: none
blockers: none
handoff: 73492cd973aa91dd25aea667b8c6141c494c908f is the clean green W6 functional head based directly on main at 298682a7; the callee proof can reinterpret related physical arguments at the generated declaration's exact ABI and rule out duplicate source-parameter bindings without any target-execution or translation-certificate premise
next: integration owner lands this ready slice; W6 then proves that unique addDeclarationParams output matches the source-order ABI row, establishes EnvLocalsRelated for targetFunction.toLocals, and lifts the caller runtime/cache relation to an empty-facts callee-entry frame
```
