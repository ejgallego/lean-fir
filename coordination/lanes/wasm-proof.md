# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 64f79c0b on main
functional-head: 342af289 (recursive structured simulation now includes compiler-derived generated lazy-cache hits and non-heap misses)
contract-base: 745610b0; proof-only extension over the accepted W6.7e recursion and existing concrete lazy-cache runtime contracts
clean-at-update: true
slice: The certificate-free cache slice is complete for hits and non-heap misses. Compiler inversion selects the generated cache lanes and exact initializer row. A miss takes the exact three-target-step initializer-entry prefix, recursively simulates the source-only initializer, returns through the saved call/conditional frames, executes concrete cacheSet plus both generated publications, and resumes the caller after an exact eight-target-step suffix. Exact source/target counts, result refinement, outer frames, cache state, ownership, address-space budget, closure tables, and entry-relative transports are reconstructed without a target trace or callee certificate premise. The theorem and roadmap now name the complete lazy-cache slice and state the heap-valued boundary explicitly.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof construction over accepted contracts
checks: Lean Beam update/sync/save version 80 hash e8748da368d4c09e; forced lake env lean FirTalos/ConcreteStructuredSimulation.lean (zero local warnings); lake build FirTalos.ConcreteStructuredSimulation (3110 jobs); git diff --check; make check (642 unique cases, 1844/1844 comparisons); make talos-setup (a01d01c); make talos-check (3133 jobs); all green
bug-cards: none
blockers: none
handoff: none; the lazy-cache slice landed on main at 64f79c0b and the lane is active on the next proof family.
next: Connect erased default-only source case selection to the recursive structured theorem as the first production case node: one exact source step, a zero-step target path over the compiler-identical selected branch, and unchanged entry-relative resources. Heap-valued cache misses remain behind the reachability-sensitive ordinary-token/entry-transport boundary and do not block this widening.
```
