# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 2d96f7a1 on main
functional-head: ba132524 (canonical compiler-produced structured export entry)
contract-base: fc5c07f5; proof-only packaging over the accepted recursive exact-path, structured-control, concrete runtime, and semantic-fidelity contracts
clean-at-update: true
slice: concreteStructuredFunctionEntry names the canonical initialized generated-function body state. ConcreteSupportedExport.reachesYield_reuseBudgetedStructured_generated now constructs the source and target code focus from the real supported export plus the ordinary initial ABI/cache frame, then exposes the recursive admitted fragment as exact finite source and structured-Wasm paths from canonical entries. The result retains the related yield, evolved entry-relative resources, empty outer frames, result ABI refinement, and exact endpoint world/trace observations. No caller-supplied focus, target path, resolver package, or translation certificate is a premise. The theorem deliberately retains its source evaluation derivation and is documented as a terminating-fragment boundary, not the later prefix-general ConcreteFiniteTraceCorrect theorem.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof and public entry packaging only; no source semantics, target semantics, runtime, lowering, adapter, or ABI contract changed
checks: clean rebase onto fc5c07f5; Lean Beam update/sync/save ConcreteStructuredSimulation version 18 hash 90b31e5488355146 with zero errors and zero warnings; forced lake env lean FirTalos/ConcreteStructuredSimulation.lean; lake build FirTalos.ConcreteStructuredSimulation (3110 jobs); git diff --check; make check (122 tests, 637 native/LCNF cases, 9 direct-machine cases, 637 native/LCNF/V8 cases, 646 unique cases and 1920/1920 indexed comparisons); Talos remains at setup a01d01c; make talos-check (3133 jobs); all green
bug-cards: none
blockers: none
handoff: none; the canonical-entry slice landed on main at 2d96f7a1 and the lane is active on the unified ranked relation.
next: Define the unified compiler-derived ranked relation over canonical and suspended structured states, then discharge its per-step advance law for the already-admitted fragment. Heap-valued lazy publication remains a separate facts-aware transport widening.
```
