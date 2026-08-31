# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 7d36f9b5
functional-head: 2d41d220
contract-base: 7d36f9b5
clean-at-update: true
slice: Derived complete zero-allocation return admission from the recursively validated production outcome. `ConcreteStructuredValidatedCodeOutcome.admit_return_of_compiler` combines residual return validation, the real compiler local layout, and the live physical state relation. `ConcreteStructuredReturnUseSiteProvenanceAt` now contributes information only on genuinely non-directional precise object-family result edges; no compiled-local equation or admission object remains client-supplied.
files: integration/talos/FirTalos/ConcreteFinalLcnfTyping.lean; docs/w6-source-admission-audit.md; docs/pass-correctness-plan.md; coordination/lanes/wasm-proof.md
contracts: W6 proof interface only. The return PA2 branch adds no source semantics, validation/lowering policy, runtime ABI/layout, symbolic instruction, generated-code, ownership, or resident-helper contract change. No future step, target path, global source invariant, or program certificate is introduced.
checks: Lean Beam update/sync/refresh/save for FirTalos.ConcreteFinalLcnfTyping (pass: zero blocking diagnostics, six pre-existing linter warnings); lake build FirTalos.ConcreteFinalLcnfTyping (pass: 3129 jobs); git diff --check (pass); make check (pass: 730 unique cases, 2172/2172 comparisons equal, exactly one trusted axiom, mailbox gates green); make talos-setup (pass: Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254); make talos-check (pass: 3190 jobs, exact build receipt 11a306aae0aecf49591b03cdf603e95cef22ff229e3369a2c8a9ca70dd75820c)
bug-cards: none
blockers: The 158 product-observed non-refining argument uses are exactly `tobject -> object`; W7 origin census request `W6-W7-20260831-002` is open to determine the smallest compiler-owned provenance analysis. PA3 also retains return producer origin, closure ingress, lazy-miss backend coverage, and schema/layout-sensitive field gaps.
handoff: clean W6 functional head `2d41d220`, based exactly on accepted main `7d36f9b5`; ready for fast-forward integration
next: Factor the shared precise producer-origin analysis used by `ConcreteStructuredReturnUseSiteProvenanceAt` and `ConcreteStructuredDirectCallArgumentsAt`, consume census `W6-W7-20260831-002`, then wire both completed branches into the whole current-step admission dispatcher.
```
