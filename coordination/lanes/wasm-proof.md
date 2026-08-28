# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: a4543bd67f4587586183da69307818469dbf3ca2
functional-head: a4543bd67f4587586183da69307818469dbf3ca2
contract-base: a4543bd67f4587586183da69307818469dbf3ca2
clean-at-update: true
slice: Thread ConstructorSchema and WitnessAgrees into the closed validated simulation and use them to replace the universal-witness premises of FVar and erased object-field admission.
files: integration/talos/FirTalos/ConcreteCompilerCorrectness.lean; integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/FirTalos/ConcreteResumableWasm.lean; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: pending proof-side simulation relation extension; no source semantics, ABI, layout, or emitted-code change intended
checks: pending
bug-cards: FIR-BUG-wasm-none-object-field-kind-admission
blockers: none
handoff: Active on wasm/talos-runtime; not ready for integration.
next: Select the smallest relation parameterization that shares one evolving schema between source typing and the active witness without disturbing witness-independent effect contracts.
```
