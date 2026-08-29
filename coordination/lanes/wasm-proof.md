# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 8020cac5f9527d7e23aa6d071ebf63d80c3bfc78
functional-head: a0e9f1fe30668651f3914db06822a99058ed8292
contract-base: 8020cac5f9527d7e23aa6d071ebf63d80c3bfc78
clean-at-update: true
slice: Expose the exact initial-witness validated relation at the canonical export root and prove ConcreteSupportedExport.finiteTraceCorrect_of_schemaSourceInvariant over one agreeing schema, its hereditary source invariant, and independent finite resource laws.
files: integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/FirTalos/ConcreteResumableWasm.lean; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: additive proof-facing export bridge only; source semantics, semantic ABI, concrete runtime/layout, lowering, emitted code, and established compatibility theorems unchanged
checks: Lean Beam sync/save ConcreteStructuredValidation and ConcreteResumableWasm (pass); git diff --check (pass); lake build FirTalos.ConcreteResumableWasm (pass, 3128 jobs); make check (pass, 730 unique validation cases and 2172/2172 equal comparisons); make talos-setup (pass, Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254); make talos-check (pass, 3182 jobs)
bug-cards: none
blockers: none
handoff: ready for integration from clean branch wasm/talos-runtime at the containing status commit
next: Define the final-LCNF semantic type/provenance invariant that instantiates this theorem, beginning with source return ABI and constructor object-field typing; keep finite runtime/address-space safety independent.
```
