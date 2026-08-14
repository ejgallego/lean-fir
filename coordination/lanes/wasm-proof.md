# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 7e5f31f3 on main
functional-head: 8262bd21
contract-base: 7e5f31f3; consumes the accepted trusted resident array-call stack and changes no shared runtime or generation contract
clean-at-update: true
slice: W6 closes validated yielded pop/resumption for direct and saturated caller frames, including arbitrary target-only case-label prefixes. The proof discovered and repaired a real relation gap: the prior static/resource agreement and suspended validation proofs hid caller result ABIs independently, so proof irrelevance could not justify that the restored continuation used the dynamic caller's result kind. The strengthened relation carries a branch-exact explicit caller-ABI spine, preserves it across every existing active/ready/return transition, and uses it to reconstruct the exact validated caller after the concrete two-step direct pop or matcher-count-plus-five saturated pop.
files: integration/talos/FirTalos/ConcreteStructuredValidation.lean; coordination/lanes/wasm-proof.md
contracts: none; proof-only strengthening of the existing concrete structured validation relation and its agreement with the unchanged production static/resource stack
checks: Lean Beam update/sync/save PASS with zero errors for FirTalos/ConcreteStructuredValidation.lean; direct lake build FirTalos.ConcreteStructuredValidation FirTalos PASS (3148 jobs); rebased onto main 7e5f31f3; post-rebase git diff --check PASS; post-rebase direct lake build FirTalos.ConcreteStructuredValidation FirTalos PASS (3148 jobs); post-rebase make check PASS (125 tests, 710 unique cases, 2112/2112 comparisons); post-rebase make talos-check PASS (3148 jobs)
bug-cards: none
blockers: none
handoff: Ready to fast-forward main from 7e5f31f3 through functional head 8262bd21 and this clean mailbox commit. The functional commit changes only the W6-owned structured validation proof module; this status commit changes only the wasm-proof mailbox.
next: Prove the validated lazy-cache publication branch, which removes the cache marker and restores the same bind validation at the external-bind administrative state. Then close external-bind resumption and validator-to-current-step admission before assembling the universal one-step and finite-trace theorems.
```
