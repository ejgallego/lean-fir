# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 2693f59350c8f54b3b84b0a7ce1d9bcabe509f02
functional-head: 2693f59350c8f54b3b84b0a7ce1d9bcabe509f02
contract-base: 2693f59350c8f54b3b84b0a7ce1d9bcabe509f02
clean-at-update: true
slice: Introduce the schema-aware current-node admission/dispatcher boundary so the ordinary code branch consumes active ConstructorSchema typing plus WitnessAgrees for FVar and erased object-field writes.
files: integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/FirTalos/ConcreteResumableWasm.lean; integration/talos/PLAN.md; bugs/FIR-BUG-wasm-none-object-field-kind-admission.md; coordination/lanes/wasm-proof.md
contracts: pending proof-side admission and simulation-relation extension; no source semantics, ABI, concrete layout/runtime operation, or emitted-code change intended
checks: pending
bug-cards: FIR-BUG-wasm-none-object-field-kind-admission
blockers: none
handoff: Active on wasm/talos-runtime; not ready for integration.
next: Factor the non-object-field admission cases, add the two schema-specific alternatives, and prove the validated ordinary-code dispatcher selects the active successors without reconstructing universal witness facts.
```
