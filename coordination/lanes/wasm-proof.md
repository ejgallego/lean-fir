# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: released
base: 638e05a2c00c8c5056ec67c4bb7fa73d8a16ff96
functional-head: 176cdbc779aaa2cab5f87e4551ce6d0d469549dc
contract-base: 638e05a2c00c8c5056ec67c4bb7fa73d8a16ff96
clean-at-update: true
slice: Added the state-local ready/preserved source-invariant interface, its canonical hereditary instance, and a validated global relation paired with that invariant. The preferred export theorem now constructs finite-prefix correctness from initial semantic safety without any target path or future execution premise. Factored invariant-free source admission for reference-count operations, deletion, tag mutation, and USize field mutation while retaining ordinary-increment headroom in the independent runtime-resource law.
files: integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/FirTalos/ConcreteResumableWasm.lean; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: none; proof-side theorem and source semantic invariant interfaces only
checks: Lean Beam update/sync/save FirTalos/ConcreteStructuredValidation.lean and FirTalos/ConcreteResumableWasm.lean (green); forced lake build FirTalos.ConcreteStructuredValidation FirTalos.ConcreteResumableWasm (green); git diff --check (green); make check (green, 730 unique differential cases and 2172/2172 comparisons); make talos-setup (green); make talos-check (green, 3182 jobs)
bug-cards: none
blockers: none
handoff: Accepted on main through integration head 3ffe30f1049dfe46f162567ba22a74e400ea32f2.
next: Derive root hereditary readiness from final-LCNF semantic typing, starting with return and descriptor-bearing field/case families; resource-safe finite-prefix budgeting remains orthogonal.
```
