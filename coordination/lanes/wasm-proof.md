# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: c025081e on main
functional-head: f8eac2ca (recursive structured simulation now includes successful ordinary recursive decrement)
contract-base: 745610b0; proof-only extension over the accepted W6.7e recursion and existing concrete lazy-cache runtime contracts
clean-at-update: true
slice: The source-only recursive admission and generated structured simulation now include OrdinaryDecrementEffectSupported. Compiler inversion fixes the exact local-read/imported-call fragment, and concrete recursive-release refinement derives its two structured target steps, updated heap, cursor preservation, capacity transport, and closure-aware runtime relation. ReuseCapacityEntryRelativeFrame.ofReplaceHeapEffectStep factors the common same-witness heap-effect reconstruction and is used by both increment and decrement. The main theorem composes one exact source effect step with the two target steps and the recursively compiled continuation, preserving exact counts, enclosing frames, pure external laws, ownership, cache globals, closure tables, and entry-relative transports without a target trace or translation certificate.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof construction over accepted contracts
checks: Lean Beam update/sync/save version 126 hash 877fb967ab370873 (zero local warnings); forced lake env lean FirTalos/ConcreteStructuredSimulation.lean (zero local warnings); lake build FirTalos.ConcreteStructuredSimulation (3110 jobs); git diff --check; make check (642 unique cases, 1844/1844 comparisons); Talos remains at setup a01d01c; make talos-check (3133 jobs); all green
bug-cards: none
blockers: none
handoff: ready from base c025081e at functional head f8eac2ca; worktree was clean before this mailbox update.
next: Land this slice, then add successful explicit deletion through its compiler-generated unary-host prefix. Keep mutation effects, heap-valued lazy publication, and saturated closure calls as separate slices.
```
