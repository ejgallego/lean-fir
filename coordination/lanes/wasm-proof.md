# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: f7e46bc32ce964bea7ce28ff0410f09b88920222
functional-head: 0f2b8f0f258cfbf263f4e58d8d0b730652d7b464
contract-base: f7e46bc32ce964bea7ce28ff0410f09b88920222
clean-at-update: true
slice: Aligned the W6, pass-composition, and object-provenance roadmaps around eliminating the arbitrary source-invariant premise through guarded schema-aware production admission; recorded PA0-PA4, the backward-composition gate, the branch audit, and the minimal consumer-driven provenance strategy.
files: integration/talos/PLAN.md; docs/pass-correctness-plan.md; docs/wasm-object-carrier-provenance-plan.md; coordination/lanes/wasm-proof.md
contracts: documentation only; no semantic, ABI, layout, lowering, proof, or emitted-code contract changes
checks: git diff --check (pass); make check (pass: 730 unique validation cases, 2172/2172 comparisons equal, coverage/trusted-assumption/mailbox gates green); make talos-setup (pass: Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254); make talos-check (pass: 3189 jobs, receipt 99b4ae3d28fd90e22fb9e5d780b608ce629d9141a31a376ccce96ce09b3f89dd)
bug-cards: none
blockers: none
handoff: ready for integration from the frozen wasm/talos-runtime branch; functional documentation checkpoint 0f2b8f0f258cfbf263f4e58d8d0b730652d7b464 is based on f7e46bc32ce964bea7ce28ff0410f09b88920222
next: PA0: audit each ConcreteStructuredSourceAdmissionSafeAt and schema-aware branch against the guarded validated relation; then strengthen only the missing reusable provenance facts, prove production compiler source-admission safety, and instantiate the existing admission-laws finite-trace theorem before another backward pass hop.
```
