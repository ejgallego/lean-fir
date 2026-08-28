# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 2e5779aa7149e3f08151e4c298a5894fb93fadd5
functional-head: 2e5779aa7149e3f08151e4c298a5894fb93fadd5
contract-base: 2e5779aa7149e3f08151e4c298a5894fb93fadd5
clean-at-update: true
slice: Lift witness-unchanged direct, saturated, lazy, external-ready, external-bind, and return administrative successors into ConcreteStructuredValidatedCodeGlobalOutcomeAt and the schema-global relation.
files: integration/talos/FirTalos/ConcreteResumableWasm.lean; integration/talos/PLAN.md; bugs/FIR-BUG-wasm-none-object-field-kind-admission.md; coordination/lanes/wasm-proof.md
contracts: additive proof-side successor theorems only; source semantics, semantic ABI, concrete runtime/layout operations, emitted code, and established validated/finite-trace relations unchanged
checks: pending
bug-cards: FIR-BUG-wasm-none-object-field-kind-admission
blockers: none
handoff: active
next: Prove the administrative successors preserve the witness-indexed relation; classify any helper that genuinely extends the witness into the following allocation/extension slice instead of weakening the index.
```
