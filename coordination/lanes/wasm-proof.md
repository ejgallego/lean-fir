# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 2a870967 on main
functional-head: 19778649 (relation-wide pointwise source-step advance with generated call-row selection, ranked silence, and admission-free dynamic successors)
contract-base: 2a870967; accepted direct and saturated pointwise call cores and current compiler/runtime contracts
clean-at-update: true
slice: Proved ConcreteStructuredCodePointwiseRel.advance for return, direct-value, generated named-call, and exactly saturated closure-call nodes. The theorem accepts one ordinary source step, constructs the finite target path and exact production callee row internally, returns an honest code/direct-ready/saturated-ready/returned successor sum, and proves compiler-rank descent whenever the target path is empty. Dynamic code successors carry an admission-free core; withAdmission attaches fresh local admission only after that successor is known.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; bugs/FIR-BUG-wasm-none-pointwise-saturated-admission.md; coordination/lanes/wasm-proof.md
contracts: none; proof relation and roadmap only
checks: Lean Beam update/sync/save FirTalos/ConcreteStructuredSimulation.lean (version 30, 0 errors); lake build FirTalos.ConcreteStructuredSimulation (3110 jobs, pass); git diff --check (pass); make check (pass, 653-case native/LCNF/V8 and all coverage policies green); make talos-setup (Talos a01d01c); make talos-check (3133 jobs, pass)
bug-cards: FIR-BUG-wasm-none-pointwise-saturated-admission (fixed by state-indexing exact saturation resolution and shared capture-retain capacity)
blockers: none
handoff: ready for integration at functional head 19778649; branch status commit contains this mailbox update
next: Close direct-ready, saturated-ready, and returned outcomes under the global relation, attach fresh admission at newly reached code nodes, then widen the same advance law to external, lazy, case, and effect operations.
```
