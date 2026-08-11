# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 5dfa5778 on main
functional-head: fc86daf1 (saturated per-step staging and structured silence rank)
contract-base: 5dfa5778; proof work over the accepted structured compiler/runtime contracts; intervening mapped-owner proofs and recursive-release fixtures change no W6 contract
clean-at-update: true
slice: Added the tenth unified control shape for pre-entry saturated calls. advance_saturatedCall_stage matches the source staging step with a reflexive target path; the ready-focus advance_enter theorem matches the single closure-consumption step with compiler-derived first-matcher selection, capture/argument execution, and generated callee entry while returning the evolved cache frame and matcher store/capacity transports. compilerStructuredControlRank now combines source control phase with recursive silence depth, proving strict descent for empty-argument staging, persistent ownership erasure, and nested default-only case erasure; advance_defaultOnlyCase_ranked exposes the latter exact local transition.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof relation and roadmap only
checks: git diff --check PASS; Lean Beam post-rebase update/sync PASS at version 1 with zero errors; lake build FirTalos.ConcreteStructuredSimulation PASS (3110 jobs) before rebase and post-rebase make talos-check PASS (3133 jobs); post-rebase make check PASS (649/649 source/LCNF/V8, 9/9 direct machine, 1947/1947 three-backend results, 1956/1956 indexed comparisons, 658 unique cases, 6563 machine steps, 116 tag floors, 221 semantic domains, findings 0; bug-card and trusted-assumption audits PASS)
bug-cards: none
blockers: none
handoff: ready for integration owner to fast-forward main from 5dfa5778 through the branch status commit containing functional-head fc86daf1
next: Define the non-terminating pointwise source-admission/resource relation and assemble the relation-wide per-source-step advance theorem using the ten control constructors and compilerStructuredControlRank.
```
