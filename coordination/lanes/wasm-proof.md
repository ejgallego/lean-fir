# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 64f78f3b on main
functional-head: 797284f2 (recursive structured simulation now includes compiler-erased persistent ownership effects)
contract-base: 745610b0; proof-only extension over the accepted W6.7e recursion and existing concrete lazy-cache runtime contracts
clean-at-update: true
slice: The source-only recursive admission and generated structured simulation now include PersistentOwnershipEffectSupported. Each persistent inc/dec takes exactly one interpreter step while production compilation erases the operation, so the target path is reflexive and execution recurses immediately on the compiler-derived continuation. The theorem retains exact source/target counts, the complete entry-relative cache/resource invariant, and both enclosing frame stacks without a target trace or translation certificate. The W6.7 roadmap now separates this completed erased family from ordinary ownership and mutation effects.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof construction over accepted contracts
checks: Lean Beam update/sync/save version 110 hash 182cbed64987eb84 (zero local warnings); forced lake env lean FirTalos/ConcreteStructuredSimulation.lean (zero local warnings); lake build FirTalos.ConcreteStructuredSimulation (3110 jobs); git diff --check; make check (642 unique cases, 1844/1844 comparisons); Talos remains at setup a01d01c; make talos-check (3133 jobs); all green
bug-cards: none
blockers: none
handoff: none; the persistent ownership slice landed on main at 64f78f3b and the lane is active on ordinary increment.
next: Add ordinary reference-count increment to the same recursive relation by reifying its generated local/import prefix and applying the existing entry-relative effect refinement. Keep decrement/delete, heap-valued lazy publication, and saturated closure calls as separate slices.
```
