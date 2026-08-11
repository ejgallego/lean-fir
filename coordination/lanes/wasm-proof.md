# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 64f78f3b on main
functional-head: 0addca73 (recursive structured simulation now includes successful ordinary reference-count increment)
contract-base: 745610b0; proof-only extension over the accepted W6.7e recursion and existing concrete lazy-cache runtime contracts
clean-at-update: true
slice: The source-only recursive admission and generated structured simulation now include OrdinaryIncrementEffectSupported. A reusable unary-host lemma reifies the compiler-derived local-read/imported-call fragment as exactly two structured steps. Concrete increment refinement supplies the updated heap, and the existing representation transports rebuild the full pure-external/ownership/cache/closure-table/entry-relative frame before recursion. The main theorem composes one exact source effect step with those two target steps and the recursively compiled continuation, preserving exact counts and enclosing frames without a target trace or translation certificate.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof construction over accepted contracts
checks: Lean Beam update/sync/save version 121 hash d1d80eaea8c4c7bf (zero local warnings); forced lake env lean FirTalos/ConcreteStructuredSimulation.lean (zero local warnings); lake build FirTalos.ConcreteStructuredSimulation (3110 jobs); git diff --check; make check (642 unique cases, 1844/1844 comparisons); Talos remains at setup a01d01c; make talos-check (3133 jobs); all green
bug-cards: none
blockers: none
handoff: Ready to fast-forward main with functional head 0addca73; the containing mailbox commit is resolved from wasm/talos-runtime.
next: After integration, add successful ordinary decrement using the same exact unary-host prefix boundary and its recursive release/transport theorem. Keep delete, heap-valued lazy publication, and saturated closure calls as separate slices.
```
