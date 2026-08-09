# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 480c15e7 on main
functional-head: bea8c53a
contract-base: 480c15e7 on main; static closure-candidate resolution and recursive whole-export correctness are linked/accepted
clean-at-update: true
slice: Derived the exact compiler closure-candidate rows by inverting successful adaptation of each actual nested dispatch chain; specialized supported-host alignment to closureMatches; removed caller-supplied resolver packages from the recursive generated-declaration induction, closure runtime APIs, and ConcreteSupportedExport.correct_reuseCapacityProductionHereditary
files: integration/talos/FirTalos/ConcreteSupportedExportCorrectness.lean; integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/PLAN.md; integration/talos/README.md; coordination/lanes/wasm-proof.md
contracts: none; no shared semantic, ABI, concrete-layout, resident-helper, or artifact change; proof packaging now derives existing compiler, adapter, and host facts internally
checks: Lean Beam save ConcreteSupportedExportCorrectness 0 errors (source 0a06e727998d2008); Lean Beam save ConcreteReuseCapacityCacheCorrectness 0 errors, 17 pre-existing warnings (source 55f17405c67ef890); lake build FirTalos.ConcreteReuseCapacityCacheCorrectness FirTalos.ConcreteReuseCapacitySupportedExportCorrectness passed (3104 jobs); git diff --check passed; make check passed (642 unique cases, 1844/1844 comparisons equal, 0 findings, 113 bug cards); make talos-setup passed at Talos a01d01c778b794dd00956748a067b6793c2c9f9b; make talos-check passed (3125 jobs)
bug-cards: none
blockers: none
handoff: Land functional-head bea8c53a plus this ready mailbox; the public finite whole-export theorem no longer accepts a resolver/certificate premise
next: State the finite-trace weak-simulation theorem over the self-contained generated execution relation, then extend the structural proof from terminating derivations to finite observations without requiring source termination
```
