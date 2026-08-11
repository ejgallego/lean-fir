# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: d2714991 on main
functional-head: 5a6143c8 (hereditary exact saturated-closure execution and caller restoration)
contract-base: d2714991; proof-only extension over the accepted exact structured-control, concrete runtime, and semantic-fidelity contracts
clean-at-update: true
slice: ReuseCapacityStructuredPureExternalLazyCodeEvaluates now admits exactly saturated closure applications recursively. ConcreteStructuredSaturatedCallEntryFocus relates the exact source staging/consumption pair to the production matcher, capture/argument, and generated call-entry prefix. Its hereditary cache-frame laws run the recursive callee in the actual generated declaration row, return through the one-result call frame and every failed/selected matcher label, restore the evolved caller ownership/cache/budget frame, bind the result, and continue recursively. ClosureAllocationsAbiAligned is required once at the theorem entry and transported through cumulative descriptor persistence. Exact source and target path lengths and outer frame equality are retained; no target trace, callee execution package, or translation certificate is a premise.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof construction over accepted contracts; the strengthened entry-ABI premise records existing static closure-allocation metadata and changes no runtime or compiler contract
checks: clean rebase onto d2714991; Lean Beam 0.2.0-beta (source 662b514f) update/sync/save ConcreteStructuredSimulation version 17 hash 2fe7a06eba4d31ed with zero errors and zero warnings; forced lake env lean FirTalos/ConcreteStructuredSimulation.lean; lake build FirTalos.ConcreteStructuredSimulation (3110 jobs); git diff --check; post-rebase make check (122 tests, 637 native/LCNF cases, 9 direct-machine cases, 637 native/LCNF/V8 cases, 646 unique cases and 1920/1920 indexed comparisons); Talos remains at setup a01d01c; post-rebase make talos-check (3133 jobs); all green
bug-cards: none
blockers: none
handoff: ready for integration; resolve the containing status commit from wasm/talos-runtime and fast-forward main from d2714991.
next: Expose the recursive exact-path fragment at the compiler-produced export/finite-trace boundary, then continue admission widening. Heap-valued lazy publication remains the separate facts-aware transport redesign.
```
