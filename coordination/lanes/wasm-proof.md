# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 2ad732443badfdfa8e7de76193f93f3ec6c0d9f2
functional-head: f57c4e0a
contract-base: 2ad732443badfdfa8e7de76193f93f3ec6c0d9f2
clean-at-update: true
slice: Completed the first PA1 case slice. Production Wasm admission now requires constructor-prefix/optional-final-default case order. Residual validation projects that Boolean fact into ConcreteStructuredCaseAltsNormalized, removing case normalization from ConcreteStructuredCaseSafeAt. The supported default-case fixture and its exact Talos simulation now use normalized order; the former default-before-constructor shape is retained as a fail-closed whole-program regression. The PA0 matrix consequently narrows from 7A/3B/10C to 7A/5B/8C: scalar and default-only case work are hidden-interface tasks, while object cases retain the genuine constructor/tag provenance gap.
files: Fir/Wasm/WellFormed.lean; Fir/Wasm/Examples.lean; coordination/BOARD.md; docs/pass-correctness-plan.md; docs/w6-source-admission-audit.md; integration/talos/PLAN.md; integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/FirTalos/Correctness/FunctionDefaultCaseExample.lean; coordination/lanes/wasm-proof.md
contracts: WASM-NORMALIZED-CASE-TABLE-ADMISSION strengthens production validation only for non-normalized case tables; no lowering instruction, emitted code, runtime, ABI, layout, helper signature, ownership rule, or behavior changes for previously accepted normalized programs
checks: Lean Beam Fir.Wasm.Examples, ConcreteStructuredValidation, and FunctionDefaultCaseExample update/sync/save (pass, zero errors); lake build Fir.Wasm.Examples (pass: 13 jobs); lake -d integration/talos build FirTalos.ConcreteStructuredValidation (pass: 3127 jobs); lake -d integration/talos build FirTalos.Correctness.FunctionDefaultCaseExample (pass: 3058 jobs); git diff --check (pass); make check (pass: 730 unique validation cases, 2172/2172 comparisons equal, coverage/trusted-assumption/mailbox gates green, exactly one trusted axiom); make talos-setup (pass: Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254); make talos-check (pass: 3189 jobs, receipt 4d6cdaeb6ef55e895bc96d3984801f9047175f212b5cd88e2f33e254f0f04ae2)
bug-cards: none
blockers: none
handoff: clean W6 integration stack `bd43f7f0` then functional head `f57c4e0a`, based exactly on `2ad73244`; ready for fast-forward integration and W7/validation rebase
next: Reshape ConcreteStructuredCaseSafeAt into branch-specific object and scalar evidence, derive scalar/default-only admission from validation plus StateRelated, then address the remaining object constructor/tag provenance. Consume W6-W7-20260830-001 before choosing the non-directional return policy.
```
