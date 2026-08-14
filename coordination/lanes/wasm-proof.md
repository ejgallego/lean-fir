# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 2e4cb265 on main
functional-head: f9beb034
contract-base: 2e4cb265; consumes the accepted validated direct/saturated caller-resumption relation and changes no shared runtime or generation contract
clean-at-update: true
slice: W6 closes validated lazy-cache publication. The strengthened global relation now has a branch-exact external-bind state carrying the unchanged caller continuation validation and hereditary tail alignment. From a validated yielded lazy caller, the new theorem unwinds any target-only case-label prefix, proves the established seven-step concrete cache publication path, removes exactly the source cache marker, preserves the concrete cache/resource/ABI invariants, and reconstructs the validated external-bind state without weakening to the production relation.
files: integration/talos/FirTalos/ConcreteStructuredValidation.lean; coordination/lanes/wasm-proof.md
contracts: none; proof-only extension of the existing concrete structured validation relation over the unchanged production lazy-cache publication and external-bind protocols
checks: Lean Beam update/sync/save PASS with zero errors for FirTalos/ConcreteStructuredValidation.lean; direct lake build FirTalos.ConcreteStructuredValidation FirTalos PASS (3148 jobs); git diff --check PASS; make check PASS (125 tests, 710 unique cases, 2112/2112 comparisons); make talos-check PASS (3148 jobs)
bug-cards: none
blockers: none
handoff: Ready to fast-forward main from 2e4cb265 through functional head f9beb034 and this clean mailbox commit. The functional commit changes only the W6-owned structured validation proof module; this status commit changes only the wasm-proof mailbox.
next: Close validated external-bind resumption into ordinary validated compiler code. Then prove validator-to-current-step admission and assemble the universal one-step and finite-trace theorems.
```
