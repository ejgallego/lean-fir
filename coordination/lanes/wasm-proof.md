# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: bc72d23f on main
functional-head: 66a9905a (recursive structured simulation now includes erased object-field mutation)
contract-base: 745610b0; proof-only extension over the accepted W6.7e recursion and existing concrete lazy-cache runtime contracts
clean-at-update: true
slice: The source-only recursive admission and generated structured simulation now include ObjectFieldErasedEffectSupported. A reusable local/constant host lemma reifies the compiler-derived object-local/canonical-zero/imported-call fragment as exactly three structured steps. Descriptor-slot alignment fixes the field ABI kind as erased, and ValueRel.erased alone justifies the zero word; ordinary object decoding is unchanged. The concrete slot writer derives the updated heap, cursor/capacity preservation, and same-witness runtime relation, after which the shared heap-effect theorem reconstructs the complete entry-relative frame before continuation recursion.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof construction over accepted contracts
checks: Lean Beam update/sync/save version 143 hash 054249c1b62f6e8d (zero local warnings); forced lake env lean FirTalos/ConcreteStructuredSimulation.lean (zero local warnings); lake build FirTalos.ConcreteStructuredSimulation (3110 jobs); git diff --check; make check (642 unique cases, 1844/1844 comparisons); Talos remains at setup a01d01c; make talos-check (3133 jobs); all green
bug-cards: none
blockers: none
handoff: ready from base bc72d23f at functional head 66a9905a; worktree was clean before this mailbox update.
next: Land this slice, then connect `USize` field mutation through the existing two-local binary host boundary. Keep packed-scalar mutations, heap-valued lazy publication, and saturated closure calls separate.
```
