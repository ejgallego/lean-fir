# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: c9b80cd7 on main
functional-head: db09c2ef (unified structured compiler control relation and observation law)
contract-base: c9b80cd7; proof-only unification over the accepted recursive exact-path, structured-control, concrete runtime, and semantic-fidelity contracts
clean-at-update: true
slice: ConcreteStructuredControlRel unifies the seven completed instruction-boundary control shapes: ordinary compiled code and yield, direct-call argument-ready, callee-entry, and caller-bind return, plus saturated-closure callee-entry and matcher-unwinding bind return. ConcreteStructuredControlRel.observes proves exact world/trace agreement once for every constructor. Resource and admission evidence remains an orthogonal future conjunct, so the relation does not hide remaining per-step gaps. Documentation identifies external request staging and pre-entry saturated-closure staging as the next missing constructors before the ranked advance law can be assembled.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof relation unification only; no source semantics, target semantics, runtime, lowering, adapter, ABI, or validation contract changed
checks: Lean Beam update/sync/save ConcreteStructuredSimulation version 21 hash beb8bdf1f1029845 with zero errors and zero warnings; forced lake env lean FirTalos/ConcreteStructuredSimulation.lean; lake build FirTalos.ConcreteStructuredSimulation (3110 jobs); git diff --check; pre-rebase make check and make talos-check green; clean rebase onto c9b80cd7 after closure-multiplicity fixtures landed; post-rebase make check (122 tests, 639 native/LCNF cases, 9 direct-machine cases, 639 native/LCNF/V8 cases, 648 unique cases and 1926/1926 indexed comparisons); Talos remains at setup a01d01c; post-rebase make talos-check (3133 jobs); all green
bug-cards: none
blockers: none
handoff: ready for integration at functional-head db09c2ef; worktree clean at the containing mailbox commit.
next: Add intermediate external-request and saturated-closure staging constructors, strengthen the unified relation with resource/admission evidence, then assemble the per-source-step advance law and structural rank. Heap-valued lazy publication remains a separate facts-aware transport widening.
```
