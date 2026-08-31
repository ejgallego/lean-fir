# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 29134ed5
functional-head: a4df6379
contract-base: 29134ed5
clean-at-update: true
slice: Closed the remaining static generated lazy-cache environment premise. Internal-function and external-import lowering-table theorems recover exact singleton result lanes; `LazyCacheResultKindsAligned.ofSupportedPipeline` and the canonical generated-environment constructor now require no cache-specific client fact.
files: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean; docs/w6-source-admission-audit.md; docs/pass-correctness-plan.md; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: proof-facing canonical lazy-cache environment API drops `LazyCacheResultKindsAligned`; source semantics, production acceptance, runtime ABI/layout, symbolic instructions, generated code, ownership, and resident-helper signatures are unchanged
checks: Lean Beam refresh/save for ConcreteReuseCapacityCacheCorrectness and ConcreteCompilerCorrectnessContract (pass, zero errors); lake build FirTalos.ConcreteCompilerCorrectnessContract (pass: 3120 jobs); git diff --check (pass); make check (pass: 730 unique cases, 2172/2172 comparisons equal, exactly one trusted axiom, mailbox gates green); make talos-setup (pass: Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254); make talos-check (pass: 3189 jobs, receipt 72e5a049d57cd701c54420dc18e081415356770c2e9c374f5ad8b00846835f97)
bug-cards: none
blockers: Static lazy-cache generation is closed; only the row-6/7 dynamic hit/miss current-step admission exports remain for this family. PA3 also retains the known non-directional object-family producer-origin, closure-ingress, and schema/layout-sensitive field gaps.
handoff: clean W6 functional head `a4df6379`, based exactly on accepted main `29134ed5`; ready for fast-forward integration
next: Factor lazy hit/miss current-step admission from the validated current relation and runtime lookup, without redesigning the relation or introducing a source invariant.
```
