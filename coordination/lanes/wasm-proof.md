# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 635f07d1
functional-head: 566459aa
contract-base: 635f07d1
clean-at-update: true
slice: Replaced the invalid blanket directional argument premise at ordinary direct calls with exact current-node semantic ingress. `SemanticArgumentsAtAbi` follows source argument syntax at the callee parameter ABI, successful `evalArgs` yields `SemanticValuesAtAbi`, and `ConstructorArgumentsRelated.ofSemanticValuesAtAbi` reclassifies the unchanged physical row. `SemanticArgumentsAtAbi.ofKindsRefine` plus the existing live state relation discharges every directional row automatically. `directInternalCallBoundary` now constructs its complete static compiler admission unconditionally; only semantic origin for the observed non-refining `tobject -> object` uses remains.
files: integration/talos/FirTalos/ConcreteRuntime.lean; integration/talos/FirTalos/ConcreteCompilerCorrectness.lean; integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/FirTalos/ConcreteFinalLcnfTyping.lean; docs/w6-source-admission-audit.md; docs/pass-correctness-plan.md; coordination/lanes/wasm-proof.md
contracts: W6 proof interface only. `DirectInternalCallSite` now carries semantic value-row typing at the parameter ABI instead of `kindsRefine`; no source semantics, production validation/lowering, runtime ABI/layout, symbolic instruction, generated-code, ownership, or resident-helper contract changed.
checks: Lean Beam sync/save for FirTalos.ConcreteRuntime, FirTalos.ConcreteCompilerCorrectness, and FirTalos.ConcreteReuseCapacityCacheCorrectness (pass: zero blocking diagnostics); lake build FirTalos.ConcreteStructuredSimulation (pass: 3127 jobs); lake build FirTalos.ConcreteFinalLcnfTyping (pass: 3129 jobs); git diff --check (pass); make check (pass: 730 unique cases, 2172/2172 comparisons equal, exactly one trusted axiom, mailbox gates green); make talos-setup (pass: Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254); make talos-check (pass: 3190 jobs, exact build receipt 7873f274a4e88e8151314c259ad75bd4785af18b90c83c09cae9f2df12b5a2aa)
bug-cards: none
blockers: The 158 product-observed non-refining argument uses are exactly `tobject -> object`; W7 origin census request `W6-W7-20260831-002` is open to determine the smallest compiler-owned provenance analysis. PA3 also retains return producer origin, closure ingress, lazy-miss backend coverage, and schema/layout-sensitive field gaps.
handoff: clean W6 functional head `566459aa`, based exactly on accepted main `635f07d1`; ready for fast-forward integration
next: Use the producer-origin census to implement the minimal compiler-owned precise-value analysis for `tobject -> object`, then construct direct-call source admission from the recursively validated outcome without a caller provenance map.
```
