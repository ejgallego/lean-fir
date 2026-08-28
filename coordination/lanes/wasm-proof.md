# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: released
base: 92f60ba255f7b2cd7ac525fe5d97b5fedd5d6131
functional-head: 619f59ae3b4e9dd04515b3d0cd6a54d1bc5ef32d
contract-base: 92f60ba255f7b2cd7ac525fe5d97b5fedd5d6131
clean-at-update: true
slice: Added precise use-site SemanticBindingAtAbi and derived active-return source admission from it. Formalized that a coarse tobject storage kind cannot replace precise semantic result typing. Proved a checked counterexample showing the current universally witness-quantified object-field alignment cannot follow from MachineState alone, sharpened the existing compiler bug card, and redirected the roadmap toward retained constructor-schema provenance related at the validated source/target boundary.
files: integration/talos/FirTalos/ConcreteRuntime.lean; integration/talos/FirTalos/ConcreteStructuredValidation.lean; bugs/FIR-BUG-wasm-none-object-field-kind-admission.md; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: none; proof-side source typing and diagnostic theorem only
checks: Lean Beam update/sync/save FirTalos/ConcreteRuntime.lean, FirTalos/ConcreteStructuredValidation.lean, and downstream FirTalos/ConcreteResumableWasm.lean (green); forced 3128-job module cone (green); git diff --check (green); make check (green, 730 unique cases and 2172/2172 comparisons); make talos-setup (green); make talos-check (green, 3182 jobs, receipt c3b430008f65ff9c4655dc5174892b8ab51716e3f2cabece64c3c17d5fefa222)
bug-cards: FIR-BUG-wasm-none-object-field-kind-admission (confirmed; evidence sharpened, not fixed)
blockers: none
handoff: Accepted on local main through exact clean tracked handoff 4924332c26637e9f17897e9eceb3853fa61d9d95.
next: Define constructor-schema provenance plus its agreement with the active refinement witness, then replace the universal object-field source assumption at the combined source/target relation boundary.
```
