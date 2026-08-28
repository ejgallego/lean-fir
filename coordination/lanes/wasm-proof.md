# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: a4543bd67f4587586183da69307818469dbf3ca2
functional-head: b424927dda88585629a25d21b6c702292a929529
contract-base: a4543bd67f4587586183da69307818469dbf3ca2
clean-at-update: true
slice: Added active-witness FVar and erased object-field admission, factored their common mutation transport, and proved closed validated-code successors from ConstructorSchema typing plus WitnessAgrees.
files: integration/talos/FirTalos/ConcreteRuntime.lean; integration/talos/FirTalos/ConcreteCompilerCorrectness.lean; integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/PLAN.md; bugs/FIR-BUG-wasm-none-object-field-kind-admission.md; coordination/lanes/wasm-proof.md
contracts: proof-side relation extension only; source semantics, semantic ABI, concrete layout/runtime operations, and emitted code unchanged
checks: git diff --check PASS; direct lake env lean on ConcreteRuntime, ConcreteCompilerCorrectness, ConcreteStructuredSimulation, and ConcreteStructuredValidation PASS; lake build FirTalos.ConcreteRuntime FirTalos.ConcreteCompilerCorrectness FirTalos.ConcreteStructuredSimulation FirTalos.ConcreteStructuredValidation FirTalos.ConcreteResumableWasm PASS (3128 jobs); make check PASS (730 cases, 2172/2172 comparisons); make talos-setup PASS; make talos-check PASS (3182 jobs, receipt 25254d510e767bb17b0a293cbed7a92f641b9935ac6e64ef4b1dddabec75604e)
bug-cards: FIR-BUG-wasm-none-object-field-kind-admission
blockers: none
handoff: Land functional commit b424927dda88585629a25d21b6c702292a929529 and this clean status commit. The local schema-derived field successors are complete; this does not claim the global dispatcher.
next: Extend the evolving global validated relation with constructor-schema agreement, preserve it across allocation/reuse transitions, and make the dispatcher select the two active-witness successors directly.
```
