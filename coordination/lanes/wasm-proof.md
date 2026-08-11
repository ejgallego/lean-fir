# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: f1147aad on main
functional-head: fcb697f4 (recursive structured simulation now includes successful explicit deletion)
contract-base: 745610b0; proof-only extension over the accepted W6.7e recursion and existing concrete lazy-cache runtime contracts
clean-at-update: true
slice: The source-only recursive admission and generated structured simulation now include OrdinaryDeleteEffectSupported. Compiler inversion fixes the exact local-read/imported-call fragment, and the concrete delete contract derives its two structured target steps, updated heap, cursor/capacity preservation, and runtime refinement. Physical zero is admitted only through ValueRel.erased and remains a no-op; ordinary object decoding still requires its mapped live-cell relation. The shared same-witness heap-effect theorem reconstructs the complete entry-relative frame before recursively compiling the continuation. Exact source/target counts and enclosing frames are preserved without a target trace or translation certificate.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof construction over accepted contracts
checks: Lean Beam update/sync/save version 129 hash b0823f797b20717f (zero local warnings); forced lake env lean FirTalos/ConcreteStructuredSimulation.lean (zero local warnings); lake build FirTalos.ConcreteStructuredSimulation (3110 jobs); git diff --check; make check (642 unique cases, 1844/1844 comparisons); Talos remains at setup a01d01c; make talos-check (3133 jobs); all green
bug-cards: none
blockers: none
handoff: none; the explicit deletion slice landed on main at f1147aad and the lane is active on constructor-tag mutation.
next: Connect successful constructor-tag mutation as the first mutation-family recursive case, deriving the exact generated prefix and full entry-relative frame reconstruction. Keep object-field/scalar-field mutations, heap-valued lazy publication, and saturated closure calls as separate slices.
```
