# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 1e9d4965 on main
functional-head: 9518acdc (recursive structured simulation now includes `USize` field mutation)
contract-base: 745610b0; proof-only extension over the accepted W6.7e recursion and existing concrete lazy-cache runtime contracts
clean-at-update: true
slice: The source-only recursive admission and generated structured simulation now include USizeFieldEffectSupported. Production compiler inversion reconstructs the object and `USize` locals plus the installed setter import. State refinement fixes their physical operands to i32/i64; the checked absolute-slot writer derives the updated heap, exact three-instruction structured path, cursor/capacity preservation, and same-witness runtime relation. The shared heap-effect theorem then reconstructs the complete entry-relative frame before continuation recursion.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof construction over accepted contracts
checks: Lean Beam 0.2.0-beta (source 662b514f) update/sync/save document version 3 hash bc077906782428d1 (zero local warnings); forced lake env lean FirTalos/ConcreteStructuredSimulation.lean (zero local warnings); lake build FirTalos.ConcreteStructuredSimulation (3110 jobs); git diff --check; make check; Talos remains at setup a01d01c; make talos-check (3133 jobs); all green
bug-cards: none
blockers: none
handoff: none; `USize` field mutation landed on main at 1e9d4965 and the lane is active on packed-integer scalar field mutation.
next: Connect packed-integer scalar field mutation through the existing two-local binary host boundary. Keep heap-valued lazy publication and saturated closure calls separate.
```
