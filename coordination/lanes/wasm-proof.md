# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: f1147aad on main
functional-head: 2309fbaa (recursive structured simulation now includes constructor-tag mutation)
contract-base: 745610b0; proof-only extension over the accepted W6.7e recursion and existing concrete lazy-cache runtime contracts
clean-at-update: true
slice: The source-only recursive admission and generated structured simulation now include ConstructorTagEffectSupported. Compiler inversion fixes the exact two-instruction local-read/imported-call fragment; the tag is encoded in the selected runtime import. The admitted live-constructor facts drive concrete header refinement, which derives the updated heap, cursor/capacity preservation, and runtime relation. The shared same-witness heap-effect theorem reconstructs the complete entry-relative frame before recursively compiling the continuation. Exact source/target counts and enclosing frames are preserved without a target trace or translation certificate.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof construction over accepted contracts
checks: Lean Beam update/sync/save version 132 hash 44a4df4560df8732 (zero local warnings); forced lake env lean FirTalos/ConcreteStructuredSimulation.lean (zero local warnings); lake build FirTalos.ConcreteStructuredSimulation (3110 jobs); git diff --check; make check (642 unique cases, 1844/1844 comparisons); Talos remains at setup a01d01c; make talos-check (3133 jobs); all green
bug-cards: none
blockers: none
handoff: ready from base f1147aad at functional head 2309fbaa; worktree was clean before this mailbox update.
next: Land this slice, then connect FVar object-field mutation. Its generated two-local/imported-call prefix needs an exact three-step structured path and ownership/fact transport for the replaced field. Keep `USize`/packed-scalar mutations, heap-valued lazy publication, and saturated closure calls separate.
```
