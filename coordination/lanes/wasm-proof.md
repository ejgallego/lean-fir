# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: d73fb90a298e7d7d80c8c2335537330388005479 on main; includes accepted W6 pointwise ordinary increment/decrement/delete, W7 Level1 publication, and the current Lean 4.33 shared-contract stack
functional-head: 50909de2
contract-base: d73fb90a; consumes the accepted structured-Wasm/compiler, source-semantics, concrete mutation/runtime, generic closure-call, and resident Level1 contracts without changing a shared semantic or executable runtime contract
clean-at-update: true
slice: W6.7f constructor-tag and field-mutation pointwise closure. The low-level structured mutation laws are now polymorphic in the active join-label stack. ConcreteStructuredCodeStepAdmission admits successful source/compiler constructor-tag, FVar object-field, erased object-field, USize-field, and packed-integer scalar-field operations without retaining source or target execution. Each named pointwise preservation theorem derives the canonical source step and exact generated prefix: two target steps for tag mutation and three for every field mutation. A shared proof-only transport reconstructs the admission-free continuation, entry-relative capacity/cache/closure resources, and aligned suspended supported frames from the existing concrete-runtime refinement; it is not stored in the relation. Both the local and strong supported-global dispatchers cover all five branches. The W6 roadmap now records the complete constructor/field mutation family in the stable pointwise relation.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean, integration/talos/PLAN.md, integration/talos/W6-THEOREM-ROADMAP.md, coordination/lanes/wasm-proof.md
contracts: none; proof-side current-node admission, pointwise preservation, label generalization, and roadmap clarification only
checks: branch began clean and aligned with main d73fb90a; Lean Beam update/sync/save PASS at version 3 with zero errors and save-ready module, source hash 7097e0e6188662c7; direct lake build FirTalos.ConcreteStructuredSimulation FirTalos.ConcreteResumableWasm PASS (3120 jobs); git diff --check PASS; make talos-setup PASS at Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254; make check PASS (122 harness tests, 661/661 native-LCNF, 9/9 direct-machine, 661-case native/LCNF/V8 triangle, 670 unique cases, 1992/1992 comparisons, 7176 machine steps, zero findings, 159 active bug cards, Lean 4.33 trusted-assumption gate); make talos-check PASS (3143 jobs, including the modified proof and ConcreteResumableWasm import cone); main remained synchronized through functional checkpoint
bug-cards: none
blockers: none
handoff: integration may fast-forward wasm/talos-runtime from main d73fb90a through functional head 50909de2 and this mailbox commit; no shared contract changed
next: add broader case and lazy/cache control to the pointwise relation, then close the remaining production current-step coverage and canonical export-root construction
```
