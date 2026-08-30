# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: c26ff528
functional-head: 5be90cf1
contract-base: c26ff528
clean-at-update: true
slice: Closed the complete case-family PA2 boundary after exact i64 object tags landed. Residual validation plus the successful source selection now derives default-only, scalar UInt8, and object-constructor support and constructs exact zero-allocation current-step admission. Deleted the obsolete semantic case classifier and removed its field from source readiness; no caller case invariant or schema premise remains.
files: integration/talos/FirTalos/ConcreteStructuredValidation.lean; docs/w6-source-admission-audit.md; docs/pass-correctness-plan.md; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: proof-facing source-admission API simplified by deleting the obsolete case-safety classifier and renaming case advancement to the validated theorem; source semantics, production validator acceptance, runtime ABI/layout, symbolic instructions, generated code, ownership, and resident-helper signatures are unchanged
checks: Lean Beam ConcreteStructuredValidation update/sync (pass, zero errors) and dependency refresh of ConcreteResumableWasm (pass, zero diagnostics); lake build FirTalos.ConcreteResumableWasm (pass: 3128 jobs); git diff --check (pass); make check (pass: 730 unique cases, 2172/2172 comparisons equal, exactly one trusted axiom, mailbox gates green); make talos-setup (pass: Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254); make talos-check (pass: 3189 jobs, receipt edd3671d324cd4cf48ddc926c66e16b6ee13a0ec2f18eb58972998cf3a8b84cf)
bug-cards: FIR-BUG-wasm-none-object-case-actual-tag-truncation fixed by the accepted exact-tag stack; no new card
blockers: PA3 still requires compiler-owned producer provenance for non-directional object-family return/call arguments, closure ingress, and schema/layout-sensitive field operations; W7 census W7-W6-20260830-005 confirms real tobject-to-object named-call arguments, so blanket directional validation is not sound for accepted products
handoff: clean W6 functional head `5be90cf1`, based exactly on accepted main `c26ff528`; ready for fast-forward integration
next: Factor the next compiler-derived admission family without redesigning the validated relation; prioritize a hidden-interface lazy-cache admission theorem, then the minimal tobject-to-object producer-origin carrier shared by return and named-call arguments.
```
