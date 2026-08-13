# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 7b07ebdc4f051014717237e6a4a494c21dfa3fd8 on main; includes the accepted zero-import Level1 extern-boundary publication and current Lean 4.33 shared-contract stack
functional-head: cf7ad7c5
contract-base: 7b07ebdc; consumes the accepted structured-Wasm/compiler, source-semantics, concrete-runtime, generic closure-call, and resident Level1 contracts without changing a shared semantic or executable runtime contract
clean-at-update: true
slice: W6.7f ordinary nonpersistent decrement pointwise closure. ConcreteStructuredCodeStepAdmission now admits a source-supported ordinary decrement without retaining a source execution certificate. ConcreteStructuredCodePointwiseRel derives the canonical source step and advances through the exact two-instruction `local.get; call` Wasm prefix. Its successor carries the admission-free continuation relation while preserving entry-relative capacity/cache/closure resources and every aligned suspended supported frame. Recursive owned-graph release is discharged by the existing concrete decrement refinement and its ordinary-persistence/capacity transports. The strong supported-global dispatcher inherits the branch. The W6 roadmap now records ordinary `inc` and `dec` as proved stable pointwise families and leaves delete/tag/field mutation, broader cases, and lazy/cache control explicit. The branch also retains the previously ready finite-trace bridge, current-step coverage derivation, and ordinary-increment pointwise slice, all rebased directly above this base.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean, integration/talos/PLAN.md, integration/talos/W6-THEOREM-ROADMAP.md, coordination/lanes/wasm-proof.md
contracts: none; proof-side admission, preservation, label generalization, and roadmap clarification only
checks: initial rebase onto main 3cfddfc0 PASS; Lean Beam update/sync/save PASS at version 1 with zero errors and save-ready module; direct lake build FirTalos.ConcreteStructuredSimulation FirTalos.ConcreteResumableWasm PASS (3120 jobs); pre-publication git diff --check PASS, make check PASS, and make talos-check PASS; main then advanced with the accepted W7 Level1 stack, so the complete seven-commit W6 stack rebased conflict-free onto 7b07ebdc; post-rebase make talos-setup PASS at Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254; git diff --check main..HEAD PASS; post-rebase make check PASS (122 harness tests, 661/661 native-LCNF, 9/9 direct-machine, 661-case native/LCNF/V8 triangle, 670 unique cases, 1992/1992 comparisons, 7176 machine steps, zero findings, 159 active bug cards, Lean 4.33 trusted-assumption gate); post-rebase make talos-check PASS (3143 jobs, including the modified proof and ConcreteResumableWasm import cone)
bug-cards: none
blockers: none
handoff: integration may fast-forward wasm/talos-runtime from main 7b07ebdc through functional head cf7ad7c5 and this mailbox commit; no shared contract changed
next: add explicit deletion to the pointwise relation, then tag/field mutation and the remaining production current-step coverage plus canonical export-root construction
```
