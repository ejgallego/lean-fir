# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 414c68cd on main
functional-head: 3a0508ae (recursive pointwise structured call-stack relation)
contract-base: 1fc7982e; rebased base 414c68cd adds accepted validation fixtures only and does not change W6 semantics
clean-at-update: true
slice: Added the recursive control-stack component required by the non-terminating pointwise simulation. ConcreteStructuredFrameRel relates direct and saturated saved callers at the current runtime/store/witness, transports the complete stack across runtime segments, and classifies finite-prefix yields without a callee evaluation premise. ConcreteStructuredStackRel joins that evidence to all ten local control protocols. Stack-lifted laws cover named and saturated staging, entry, and return; saturated entry transports older callers across the real matcher/closure-consumption update and establishes the callee cache frame.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof relation and roadmap only
checks: Lean Beam update/sync/save (0 errors); forced lake build FirTalos.ConcreteStructuredSimulation (pass); post-rebase git diff --check (pass); make talos-setup (pass, Talos a01d01c); post-rebase make talos-check (pass, 3133-module cone); post-rebase make check (pass, Lean/examples and interpreter/Wasm validation)
bug-cards: none
blockers: none
handoff: ready; integrate 3a0508ae from wasm/talos-runtime
next: Add the parallel resource stack and source-only pointwise admission invariant. Preserve fact maps, allocation budget, closure ABI, and admission at each successor without wrapping the terminating hereditary evaluator. Then connect target-only case-label control and assemble the relation-wide advance theorem from ConcreteStructuredStackRel and compilerStructuredControlRank.
```
