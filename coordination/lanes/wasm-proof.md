# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 8bcd7326 on main
functional-head: ff2104c1 (exact source and target entry into the compiler-resolved saturated-closure callee)
contract-base: 8bcd7326; proof-only extension over the accepted saturated dispatch/argument execution and generic Flat prerequisite
clean-at-update: true
slice: SaturatedClosureCallSite.semanticArgs_size exposes the shared source-evaluation arity fact. SaturatedClosureCallResolution.sourceStageAndEnterFinitePath reconstructs source staging and ownership-consuming closure entry in exactly two interpreter steps. targetDispatchArgumentsAndEnterFinitePath composes the real matcher fold, selected capture/argument execution, and generated enterCall step, reaching the generated callee with its exact saved call frame and every conditional label. structuredWasmLeaveReplicatedClosureLabelsFinitePath proves normal selected-body fallthrough restores the caller operand tail and residual continuation in exactly before.length + 1 target steps. No theorem accepts a target path, branch, or translation certificate.
files: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof construction over accepted contracts
checks: rebased onto 8bcd7326; Lean Beam 0.2.0-beta (source 662b514f) refresh/sync/save ConcreteReuseCapacityCacheCorrectness version 1 hash a83847e992abe157 and ConcreteStructuredSimulation version 1 hash a411bda670ebc2b4 (zero local warnings in the changed structured module); forced lake env lean FirTalos/ConcreteReuseCapacityCacheCorrectness.lean and FirTalos/ConcreteStructuredSimulation.lean; lake build FirTalos.ConcreteStructuredSimulation (3110 jobs); git diff --check; make check (122 tests, 633 native/LCNF cases, 9 direct-machine cases, 601 native/LCNF/V8 cases, 1844/1844 indexed comparisons); Talos remains at setup a01d01c; make talos-check (3133 jobs); all green after rebase
bug-cards: none
blockers: none
handoff: ready; fast-forward main from 8bcd7326 through functional head ff2104c1 and this containing mailbox status commit.
next: Run the recursive saturated callee from the exact entry, return through the saved call frame, write the selected body's result local, apply the exact conditional-label unwind, and restore the ownership/resource frame before continuation recursion. Defer heap-valued lazy publication until the entry transport is made facts-aware.
```
