# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 8020cac5f9527d7e23aa6d071ebf63d80c3bfc78
functional-head: 8020cac5f9527d7e23aa6d071ebf63d80c3bfc78
contract-base: 8020cac5f9527d7e23aa6d071ebf63d80c3bfc78
clean-at-update: true
slice: Expose the indexed validated compiler relation at the canonical export root and state the production-facing schema-indexed finite-trace theorem directly over that root.
files: integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/FirTalos/ConcreteResumableWasm.lean; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: additive proof-facing export bridge only; source semantics, semantic ABI, concrete runtime/layout, lowering, emitted code, and established compatibility theorems unchanged
checks: pending
bug-cards: none
blockers: none
handoff: active development; not ready for integration
next: Add the exact indexed export root, compose it with ConcreteStructuredSchemaSourceInvariantLaws.toFiniteTraceCorrect, then validate and checkpoint the public theorem.
```
