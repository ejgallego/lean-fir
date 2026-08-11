# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 0966e35f on main
functional-head: 37f5f6bb (direct-call current-step admission, staging, entry, hereditary result ABI, and caller-core pop)
contract-base: 0966e35f; accepted compiler/runtime contracts and local step-admission boundary
clean-at-update: true
slice: Connect generated named calls to the pointwise core without callee evaluation. Index local admission by current runtime/environment, add zero-cost named-call admission, derive exact staging and generated entry, fuse active/suspended result ABI metadata into the hereditary resource stack, and restore the caller code core on direct bind pop.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof relation and roadmap only
checks: Lean Beam update/sync/save 0 errors and 3 warnings; lake build FirTalos.ConcreteStructuredSimulation (success, 3110 jobs); git diff --check (success); make check (success, 122 interpreter tests); make talos-setup (Talos a01d01c778b794dd00956748a067b6793c2c9f9b); make talos-check (success, 3133 jobs); post-check git rebase main (already current)
bug-cards: none
blockers: none
handoff: ready for integration; worktree clean at functional head before this mailbox-only status commit
next: Repeat the same current-step/core composition for exactly saturated closure staging, matcher/entry, and saturated bind pop; then define the relation-wide control sum and fresh successor-admission classifier.
```
