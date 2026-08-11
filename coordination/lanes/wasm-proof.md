# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 59ea914f on main
functional-head: 1bc6eb40 (module-stable global outcome and certificate-free generated call-entry closure)
contract-base: 59ea914f; accepted pointwise code advance and current compiler/runtime contracts
clean-at-update: true
slice: Added ConcreteStructuredGlobalOutcome, which existentially hides the active generated function, entry anchor, ABI, and resource budget. The pointwise code law now lifts to this module-stable conclusion. Named and exactly saturated ready states enter their selected generated callees in the same global relation from only the ordinary source step; the saturated rule reconstructs exact closure consumption internally, and generated rows re-anchor the complete supported-function contract at the callee.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof relation and roadmap only
checks: Lean Beam update/sync/save FirTalos/ConcreteStructuredSimulation.lean (version 40, 0 errors); lake build FirTalos.ConcreteStructuredSimulation (3110 jobs, pass); git diff --check (pass); make check (pass, 662 unique cases and 1968 comparisons); make talos-setup (Talos a01d01c); make talos-check (3133 jobs, pass)
bug-cards: none
blockers: none
handoff: ready for integration at functional head 1bc6eb40; branch status commit contains this mailbox update
next: Retain each suspended caller's supported-function identity and canonical cache table alongside its hereditary resource scope, then close direct and saturated return-pop transitions under ConcreteStructuredGlobalOutcome. This is static compiler metadata, not a future execution certificate.
```
