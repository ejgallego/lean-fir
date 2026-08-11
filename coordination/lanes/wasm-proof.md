# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: af7f9a89 on main
functional-head: af7f9a89 (accepted certificate-free external execution checkpoint)
contract-base: af7f9a89; proof work over the accepted structured compiler/runtime contracts
clean-at-update: true
slice: Construct the missing pre-entry saturated-closure focus. The first source step stages invokeValue against a reflexive target path; the second source step will execute the compiler-derived matcher, capture/argument prefix, and generated callee entry, preserving exact per-step observations without a target certificate.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof relation and roadmap only
checks: pending
bug-cards: none
blockers: none
handoff: not ready; active proof slice
next: Prove saturated staging and entry transitions, add the control constructor, then begin the unified per-source-step advance law and structural rank.
```
