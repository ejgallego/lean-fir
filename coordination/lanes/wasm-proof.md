# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 91b2f3acbf4f6a57bf73592aa53a2f6dd02aaf30
functional-head: 565debce1d345bcf14bdcbab226cda54991520c1
contract-base: 91b2f3acbf4f6a57bf73592aa53a2f6dd02aaf30
clean-at-update: true
slice: Restructured the live verification roadmap, archived the landed pass-proof chronology, published the theorem-contract and assumption-budget tables, and created the PA0 source-admission audit scaffold with all 20 target branches mapped to the 17 source-safety constructors; classification is intentionally paused for user review.
files: Makefile; docs/pass-correctness-plan.md; docs/pass-correctness-history.md; docs/w6-source-admission-audit.md; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: documentation only plus a whole-word correction to the no-placeholders gate so exact theorem identifiers containing admit_ do not false-positive; no semantic, ABI, layout, lowering, proof, or emitted-code contract changes
checks: make no-placeholders (pass); constructor inventory count (17 source constructors, 20 target branches, 20 audit rows); git diff --check (pass); make check (pass: 730 unique validation cases, 2172/2172 comparisons equal, coverage/trusted-assumption/mailbox gates green, exactly one trusted axiom); make talos-setup (pass: Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254); make talos-check (pass: 3189 jobs, receipt 5ce3cf999a274d1e032a833723f3aad6de31b2430fa920c974ea5720db391fb2)
bug-cards: none
blockers: none
handoff: review checkpoint only at functional head 565debce1d345bcf14bdcbab226cda54991520c1; do not integrate or begin PA0 classification until the user accepts the audit boundary
next: Review whether PA2 derives schema code-step admission directly or first derives schema source safety, and agree on the minimal common result-provenance boundary before assigning A-E gap classes.
```
