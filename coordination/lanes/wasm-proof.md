# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: aecae9a404cab3e90cdbd6cfb02d23732bfe785d on main
functional-head: 7916298de190d9ed561ac850448352667596f986
contract-base: aecae9a4 on main; consumes the accepted generated-declaration parameter row, validator ABI refinement, adapter, concrete-runtime, and declaration-correctness contracts
clean-at-update: true
slice: Prove that production front-insertion plus emission reversal yields the exact source-order parameter ABI row, then compose bindParams and the related physical argument row into EnvLocalsRelated for the generated callee's toLocals frame
files: integration/talos/FirTalos/ConcreteCompilerCorrectness.lean; integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean; integration/talos/PLAN.md; this mailbox
contracts: no semantic Wasm ABI, lowering, validator, adapter, or concrete-runtime contract changed; sourceParameterBindings, parameterKindsSize, sourceParameterNamesNodup, ConstructorArgumentsRelated.resolveAt, and entryEnvLocalsRelatedOfArguments are proof-only consequences of the existing production equations
checks: PASS Lean Beam update/sync/save FirTalos/ConcreteCompilerCorrectness.lean and FirTalos/ConcreteReuseCapacityCacheCorrectness.lean plus refresh/save FirTalos/ConcreteCompilerCorrectnessContract.lean (zero errors; existing warnings only); PASS lake build FirTalos.ConcreteCompilerCorrectness FirTalos.ConcreteReuseCapacityCacheCorrectness FirTalos.ConcreteCompilerCorrectnessContract (3104 jobs); PASS make talos-setup (Talos a01d01c778b794dd00956748a067b6793c2c9f9b); PASS git diff --check; PASS make check (122 interpreter-validator tests plus repository validation plans); PASS make talos-check (3125 jobs)
bug-cards: none
blockers: none
handoff: 7916298de190d9ed561ac850448352667596f986 is the clean green W6 functional head based directly on main at aecae9a4; recursive calls can now construct the exact generated callee environment/local relation from the production call site and related argument operands, without hygiene, execution-certificate, or translation-certificate premises
next: integration owner lands this ready slice; W6 then lifts the caller's unchanged concrete runtime, failure, cache, and closure-table fields into an empty-reuse-facts callee-entry ConcreteReuseCapacityCacheFrame and starts the finite-execution hereditary induction
```
