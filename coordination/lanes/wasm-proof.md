# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 3d7803a0733acea2d06a8a0c5604cea1eec98b05 on main; includes accepted W6 pointwise ordinary increment/decrement, W7 Level1 publication, and the current Lean 4.33 shared-contract stack
functional-head: c9608bf7
contract-base: 3d7803a0; consumes the accepted structured-Wasm/compiler, source-semantics, concrete delete-erased, concrete-runtime, generic closure-call, and resident Level1 contracts without changing a shared semantic or executable runtime contract
clean-at-update: true
slice: W6.7f explicit deletion pointwise closure. ConcreteStructuredCodeStepAdmission admits a source-supported delete without retaining a source execution certificate. ConcreteStructuredCodePointwiseRel derives the canonical source step and advances through the exact two-instruction `local.get; call` Wasm prefix, returning the admission-free continuation while preserving entry-relative capacity/cache/closure resources and every aligned suspended supported frame. The theorem covers both ordinary live-object deletion and the accepted erased-value/physical-zero no-op; those branches are consequences of the existing concrete delete refinement rather than a weakened decoder or stored target execution. The strong supported-global dispatcher inherits the branch. The W6 roadmap now records the complete ordinary increment/decrement/delete ownership family in the stable pointwise relation.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean, integration/talos/PLAN.md, integration/talos/W6-THEOREM-ROADMAP.md, coordination/lanes/wasm-proof.md
contracts: none; proof-side admission, preservation, label generalization, and roadmap clarification only
checks: branch began clean and aligned with main 3d7803a0; Lean Beam update/sync/save PASS at version 1 with zero errors and save-ready module, source hash 835837af6ea37b24; direct lake build FirTalos.ConcreteStructuredSimulation FirTalos.ConcreteResumableWasm PASS (3120 jobs); git diff --check PASS; make talos-setup PASS at Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254; make check PASS (122 harness tests, 661/661 native-LCNF, 9/9 direct-machine, 661-case native/LCNF/V8 triangle, 670 unique cases, 1992/1992 comparisons, 7176 machine steps, zero findings, 159 active bug cards, Lean 4.33 trusted-assumption gate); make talos-check PASS (3143 jobs, including the modified proof and ConcreteResumableWasm import cone); main remained synchronized through checkpoint
bug-cards: none
blockers: none
handoff: integration may fast-forward wasm/talos-runtime from main 3d7803a0 through functional head c9608bf7 and this mailbox commit; no shared contract changed
next: add constructor-tag mutation to the pointwise relation, then field mutation, broader cases/lazy-cache control, and the remaining production current-step coverage plus canonical export-root construction
```
