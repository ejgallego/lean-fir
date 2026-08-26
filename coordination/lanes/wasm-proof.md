# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 0c37e6d3902cf63c5baf2c81d2b54f8807897e24, current main after validated effect-step acceptance
functional-head: 59a945c0cbbdc9ee64131d45fc6d000a01105b91
contract-base: 0c37e6d3902cf63c5baf2c81d2b54f8807897e24
clean-at-update: true
slice: Extends the pending validated-case and join-entry stack with the certificate-free active-label invariant and exact resolved-join unwinding theorem. ConcreteStructuredActiveLabelRel aligns compiler join contexts, named and anonymous adapter labels, and the active function's concrete StructuredWasmFrame.label prefix; its inactive constructor retains lexical/compiler join scope after the physical block has been consumed. ConcreteStructuredActiveLabelRel.unwindResolved proves that successful symbolic label lookup alone selects the production-compiled join body and yields an exact depth-plus-one StructuredWasmStep path across anonymous labels, nonmatching named labels, and inactive joins, ending with the matched declaration retained as an inactive lexical join. It assumes no target path, translation certificate, future execution, dispatcher admission, or termination evidence.
files: integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/FirTalos/ConcreteCompilerCorrectness.lean; integration/talos/FirTalos/ConcreteStructuredSimulation.lean; coordination/lanes/wasm-proof.md
contracts: No shared source semantics, executable runtime behavior, compiler ABI, concrete memory layout, resident-helper signature, emitter, symbolic Wasm instruction, or W7 artifact changed. The active-label relation and exact unwinding theorem are additive W6 proof-side interfaces derived from the existing production compiler, adapter lookup, and structured target step relation.
checks: Lean Beam update was run after every edit. The large ConcreteStructuredSimulation diagnostics barrier required the prescribed targeted batch fallback; lake build FirTalos.ConcreteStructuredSimulation passed all 3,126 jobs. git diff --check passed; make check passed with 719/719 source cases, 9/9 direct-machine cases, 728 unique cases, 2,166/2,166 comparisons equal, zero findings, 209 active bug cards, and 31 mailbox tests; make talos-setup completed at Talos 0e05edbc; make talos-check passed all 3,174 jobs.
bug-cards: FIR-BUG-impure-case-table-selector-determinism (existing; names the missing final-LCNF normalization phase bridge); FIR-BUG-wasm-none-return-admission-refinement-direction (existing; semantic transport and state-local return-safety boundaries solved; the global source-typing invariant/module dispatcher remains)
blockers: none
handoff: GREEN LIGHT. Consume the exact immutable checkpoint published for cumulative functional head 59a945c0 rather than following a moving branch. It is based directly at 0c37e6d3 and includes the earlier validated-case and join-entry heads. The worktree is clean at this update and every required gate passes.
next: Converge on authoritative mailbox thread W7-W6-20260826-028 and rebase onto d78d128c for the requested heap-only USize proof. Do not begin another dispatcher successor before that convergence handoff.
```
