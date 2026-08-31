# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 302d4cd7
functional-head: 30bc5522
contract-base: 302d4cd7
clean-at-update: true
slice: Closed the ordinary direct-call result half of PA2 admission. Production validation requires the effective callee result to directionally refine the source `let` ABI for non-cached calls, while nullary lazy-cache calls retain the exact object-family `leanCompatible` rule required by the complete corpus. `effectiveDeclarationResultKind?_declared_refines`, `supportedNamedCall_internal_facts`, and `ConcreteStructuredAlignedValidationState.directInternalCallBoundary` now derive declaration/result classification, result direction, and exact destination-local selection from residual validation. The boundary exposes only directional argument ingress.
files: Fir/Wasm/Examples.lean; Fir/Wasm/WellFormed.lean; integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/FirTalos/ConcreteFinalLcnfTyping.lean; docs/w6-source-admission-audit.md; docs/pass-correctness-plan.md; coordination/lanes/wasm-proof.md
contracts: `supportedNamedCall` now rejects reverse object-family result edges on ordinary non-cached calls, but deliberately retains `leanCompatible` for nullary cached declarations. W7's product census found 0 non-refining results across 11,487 result edges; the full validation corpus supplied the cache exception. Source semantics, runtime ABI/layout, symbolic instructions, generated code, ownership, and resident-helper signatures are unchanged.
checks: Lean Beam sync/save for Fir.Wasm.WellFormed, FirTalos.ConcreteStructuredValidation, and FirTalos.ConcreteFinalLcnfTyping (pass: zero edited-module errors/warnings before the final batch rebuild); lake build Fir.Wasm.Examples (pass: 13 jobs); lake build FirTalos.ConcreteFinalLcnfTyping (pass: 3129 jobs); git diff --check (pass); make check (pass: 730 unique cases, 2172/2172 comparisons equal, exactly one trusted axiom, mailbox gates green); make talos-setup (pass: Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254); make talos-check (pass: 3190 jobs, exact build receipt 313cea9a36c96b9ce2471ff6f7f7d74e71f116e27ad9f1f60e8d84209c255c22)
bug-cards: none
blockers: Ordinary direct-call argument ingress remains directional where production intentionally accepts `tobject -> object`; it requires reusable producer provenance rather than a blanket validator restriction. PA3 also retains return producer origin, closure ingress, lazy-miss backend coverage, and schema/layout-sensitive field gaps.
handoff: clean W6 functional head `30bc5522`, based exactly on accepted main `302d4cd7`; ready for fast-forward integration
next: Derive reusable named-call argument-origin reclassification from validated producer provenance, then feed it to `directInternalCallBoundary`; do not add a caller provenance map or weaken argument refinement.
```
