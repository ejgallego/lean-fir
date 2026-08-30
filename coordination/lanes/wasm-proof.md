# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 430506f8
functional-head: 3fd82c1c
contract-base: 430506f8
clean-at-update: true
slice: Closed the integration-owned lazy-cache validator boundary. The production validator now exposes initializer uniqueness and singleton-result signature accessors; `lazyCacheValidatorSound` derives `LazyCacheValidationFacts` uniformly, and both supported-pipeline generated-environment constructors no longer accept validator soundness as a client premise.
files: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean; docs/w6-source-admission-audit.md; docs/pass-correctness-plan.md; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: proof-facing lazy-cache pipeline API drops the `LazyCacheValidatorSound` parameter and consumes accepted public validator accessors; source semantics, production acceptance, runtime ABI/layout, symbolic instructions, generated code, ownership, and resident-helper signatures are unchanged
checks: Lean Beam update/sync/save for ConcreteReuseCapacityCacheCorrectness and ConcreteCompilerCorrectnessContract (pass, zero errors); lake build FirTalos.ConcreteCompilerCorrectnessContract (pass: 3120 jobs); git diff --check (pass); make check (pass: 730 unique cases, 2172/2172 comparisons equal, exactly one trusted axiom, mailbox gates green); make talos-setup (pass: Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254); make talos-check (pass: 3189 jobs, receipt 17d1aa84540123fff173821ab041619dafe4f0993d098809f4ceb9f52c9fffa7)
bug-cards: none
blockers: `LazyCacheResultKindsAligned` remains the sole static generated-environment condition before lazy hit/miss admission can be fully compiler-derived; PA3 also retains the known non-directional object-family producer-origin, closure-ingress, and schema/layout-sensitive field gaps
handoff: clean W6 functional head `3fd82c1c`, based exactly on accepted validator contract `430506f8`; ready for fast-forward integration
next: Derive exact lazy-cache declaration/result-lane alignment from supported lowering, then factor hit/miss current-step admission without redesigning the validated relation.
```
