# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 87c0299d2bfeaae6a1ad32ee87bfa00dd31fe090
functional-head: 87c0299d2bfeaae6a1ad32ee87bfa00dd31fe090
contract-base: 87c0299d2bfeaae6a1ad32ee87bfa00dd31fe090
clean-at-update: true
slice: Add a uniform active-witness projection and constructor-schema agreement companion for every validated global outcome, then establish generic preservation across witness-unchanged successors.
files: integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/FirTalos/ConcreteResumableWasm.lean; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: pending additive proof-side global relation companion; no source semantics, ABI, runtime operation, or emitted-code change intended
checks: pending
bug-cards: FIR-BUG-wasm-none-object-field-kind-admission
blockers: none
handoff: Active on wasm/talos-runtime; not ready for integration.
next: Define the witness projection without duplicating global constructors, wrap validated outcomes with ConstructorSchema.WitnessAgrees, and prove the witness-identity transport used by field mutation and administrative stutters.
```
