# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: d04851f1
functional-head: 140aee42
contract-base: d04851f1
clean-at-update: true
slice: Derived lazy-cache current-node shape from production facts. Runtime lookup selects hit or miss; validation retains only the actual `leanCompatible` result check; `ConcreteResidualLocalAlignment` derives the destination ABI from production's effective-update traversal, with a compiler-root theorem and common `let` head/continuation projections. Lazy admission no longer accepts a cache-specific destination-local or hit/miss premise.
files: integration/talos/FirTalos/ConcreteResidualLocalAlignment.lean; integration/talos/FirTalos/ConcreteFinalLcnfTyping.lean; integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/FirTalos/ConcreteStructuredValidation.lean; docs/w6-source-admission-audit.md; docs/pass-correctness-plan.md; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: proof-side `LazyCacheCallSupported` stores production `leanCompatible` rather than an unused directional refinement; lazy compiler admission consumes the generic compiler-derived residual-local alignment. Source semantics, production acceptance, runtime ABI/layout, symbolic instructions, generated code, ownership, and resident-helper signatures are unchanged.
checks: Lean Beam refresh/save for ConcreteResidualLocalAlignment (pass: zero errors/warnings), ConcreteStructuredSimulation (pass: zero errors), ConcreteStructuredValidation (pass: zero errors), and ConcreteFinalLcnfTyping (pass: zero errors); lake build FirTalos.ConcreteFinalLcnfTyping (pass: 3129 jobs); git diff --check (pass); make check (pass: 730 unique cases, 2172/2172 comparisons equal, exactly one trusted axiom, mailbox gates green); make talos-setup (pass: Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254); make talos-check (pass: 3190 jobs, receipt 79af5253db5bf967bf317bf4c912eb1ef6d60be57ecfa9227d9075c401a1d63a)
bug-cards: none
blockers: The generic residual-local row must now be carried through active and suspended validated outcomes. Lazy misses accepted by production but implemented by an external initializer or returning `.object`/`.tobject` remain a genuine backend-coverage gap. PA3 also retains the known producer-origin, closure-ingress, and schema/layout-sensitive field gaps.
handoff: clean W6 functional head `140aee42`, based exactly on accepted main `d04851f1`; ready for fast-forward integration
next: Thread `ConcreteResidualLocalAlignment` through the validated global relation using structural preservation, then consume it in compiler-derived current-step admission. Do not reintroduce a caller source invariant.
```
