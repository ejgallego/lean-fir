# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 64f79c0b on main
functional-head: a54b6dae (recursive structured simulation now includes compiler-erased default-only case selection)
contract-base: 745610b0; proof-only extension over the accepted W6.7e recursion and existing concrete lazy-cache runtime contracts
clean-at-update: true
slice: The first selected production case node is complete. The source-only recursive admission includes default-only cases; exact source semantics takes one selection step, while compiler inversion proves that production compilation erased the wrapper to the identical selected target branch. The structured target path is reflexive, recursion continues over the selected branch, and the unchanged entry-relative cache/resource frame plus exact outer frames are retained. This is the first genuine zero-target transition to feed the later compiler silence rank.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof construction over accepted contracts
checks: Lean Beam update/sync/save version 83 hash 29c2a2a6ee95d18f; forced lake env lean FirTalos/ConcreteStructuredSimulation.lean (zero local warnings); lake build FirTalos.ConcreteStructuredSimulation (3110 jobs); git diff --check; make check (642 unique cases, 1844/1844 comparisons); Talos remains at setup a01d01c; make talos-check (3133 jobs); all green
bug-cards: none
blockers: none
handoff: Ready for prompt integration on main. Base 64f79c0b; functional head a54b6dae; containing mailbox commit is resolved from wasm/talos-runtime.
next: After integration, derive an exact structured finite path for the production object/scalar case dispatcher selected by SourceCaseResult, then recurse over its compiler-selected branch with unchanged runtime resources. Heap-valued cache misses remain behind the reachability-sensitive ordinary-token/entry-transport boundary and do not block this widening.
```
