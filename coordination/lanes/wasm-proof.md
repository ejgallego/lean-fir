# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: f5b15d8e on main
functional-head: 306658b6 (recursive structured simulation now includes all supported packed-integer field mutations)
contract-base: 745610b0; proof-only extension over the accepted W6.7e recursion and existing concrete lazy-cache runtime contracts
clean-at-update: true
slice: The source-only recursive admission and generated structured simulation now include ScalarFieldEffectSupported. Production compiler inversion reconstructs both locals and the kind-indexed setter. State refinement selects i32 for UInt8/16/32 and i64 for UInt64. Four checked concrete writers supply their layout-safe memory operations, while one factored structured theorem proves the exact three-instruction target path and reconstructs the complete same-witness entry-relative frame for every width.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof construction over accepted contracts
checks: Lean Beam 0.2.0-beta (source 662b514f) update/sync/save document version 7 hash 3e366988e9389d6f (zero local warnings); forced lake env lean FirTalos/ConcreteStructuredSimulation.lean (zero local warnings); lake build FirTalos.ConcreteStructuredSimulation; git diff --check; make check; Talos remains at setup a01d01c; make talos-check (3133 jobs); all green
bug-cards: none
blockers: none
handoff: none; packed-integer scalar mutation landed on main at f5b15d8e and the lane is active on saturated closure calls.
next: Connect saturated closure calls using the existing source-only resolution, concrete matcher, argument-assembly, and recursive callee contracts. Defer heap-valued lazy publication until the entry transport is made facts-aware.
```
