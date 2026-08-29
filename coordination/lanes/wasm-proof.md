# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: d8ac1b47ebe0ce2ef4d6efc10a2924eb2772e2fb
functional-head: 937cd033f7baf2b54b2de1c7f1d211a848925daa
contract-base: d8ac1b47ebe0ce2ef4d6efc10a2924eb2772e2fb
clean-at-update: true
slice: Add reusable observable finite-prefix simulation composition, embed the ranked W6 theorem into it, bridge FIR's relational finite-stuttering pass API to the deterministic interpreter, and prove one-edge backward precomposition including an equality-pass regression.
files: integration/talos/FirTalos/Correctness/WeakSimulation.lean; integration/talos/FirTalos/ConcreteTraceSimulation.lean; integration/talos/FirTalos/ConcretePassComposition.lean; integration/talos/FirTalos.lean; coordination/lanes/wasm-proof.md
contracts: additive W6 proof-facing composition surface only; the existing ranked concrete theorem, source semantics, pass semantics, ABI, runtime/layout, lowering, and emitted code remain unchanged
checks: Lean Beam sync/save WeakSimulation, ConcreteTraceSimulation, ConcretePassComposition, and FirTalos umbrella (pass); git diff --check (pass); lake build FirTalos.ConcretePassComposition (pass, 3108 jobs); make check (pass, 730 unique validation cases and 2172/2172 equal comparisons); make talos-setup (pass, Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254); make talos-check (pass, 3183 jobs, receipt ec63d1eb3a275b7cbaa5d5c61a01bd1520288c52ee7291cde74c23d66a26d354)
bug-cards: none
blockers: none
handoff: ready for integration from clean branch wasm/talos-runtime at the containing status commit
next: Introduce the sumTo captured final-LCNF admission fixture and use it to drive generic static source typing/provenance; keep program-specific proof limited to closed syntax and entry/resource facts.
```
