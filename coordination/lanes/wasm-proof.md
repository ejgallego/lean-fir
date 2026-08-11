# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: bc72d23f on main
functional-head: 0d4ecd7b (recursive structured simulation now includes FVar object-field mutation)
contract-base: 745610b0; proof-only extension over the accepted W6.7e recursion and existing concrete lazy-cache runtime contracts
clean-at-update: true
slice: The source-only recursive admission and generated structured simulation now include ObjectFieldFVarEffectSupported. A reusable binary-host lemma reifies the compiler-derived object-local/field-local/imported-call fragment as exactly three structured steps. Descriptor-slot alignment proves the second local has the compiler-selected object-field ABI kind; the concrete slot writer derives the updated heap, cursor/capacity preservation, and same-witness runtime relation. The shared heap-effect theorem reconstructs the complete entry-relative frame before recursively compiling the continuation. Exact source/target counts and enclosing frames are preserved without a target trace or translation certificate.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof construction over accepted contracts
checks: Lean Beam update/sync/save version 136 hash d045d20df896dffb (zero local warnings); forced lake env lean FirTalos/ConcreteStructuredSimulation.lean (zero local warnings); lake build FirTalos.ConcreteStructuredSimulation (3110 jobs); git diff --check; make check (642 unique cases, 1844/1844 comparisons); Talos remains at setup a01d01c; make talos-check (3133 jobs); all green
bug-cards: none
blockers: none
handoff: none; FVar object-field mutation landed on main at bc72d23f and the lane is active on erased object-field mutation.
next: Connect erased object-field mutation through its object-local/constant-zero/imported-call prefix. Keep `USize`/packed-scalar mutations, heap-valued lazy publication, and saturated closure calls separate.
```
