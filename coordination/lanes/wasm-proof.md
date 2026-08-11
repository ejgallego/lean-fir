# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 745610b0 on main
functional-head: 91ccfe40 (recursive structured simulation now includes compiler-derived generated lazy-cache hits)
contract-base: 745610b0; proof-only extension over the accepted W6.7e recursion and existing concrete lazy-cache runtime contracts
clean-at-update: true
slice: The hit half is complete: compiler inversion selects the generated flag/value indices and unselected miss body, the cache relation supplies the populated physical value, and the recursive theorem takes the exact three-source/five-target-step path while preserving the entry-relative cache/resource frame and exact saved frames. Continue with the miss initializer entry and publication suffix.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof construction over accepted contracts
checks: Lean Beam update/sync/save version 56 hash 273e2c2f5f413931; forced lake env lean FirTalos/ConcreteStructuredSimulation.lean; lake build FirTalos.ConcreteStructuredSimulation (3110 jobs); git diff --check; make check (642 unique cases, 1844/1844 comparisons); make talos-setup (a01d01c); make talos-check (3133 jobs); all green
bug-cards: none
blockers: none
handoff: none; active proof slice
next: Split the compiler-derived miss path at the empty flag conditional, enter the exact generated initializer row under the cache/bind and label/call frames, apply the recursive structured theorem to its source-only initializer derivation, then structurally execute cacheSet, the two global publications, value load, and destination write before resuming the caller continuation.
```
