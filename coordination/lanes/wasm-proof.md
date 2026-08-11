# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: bc30ac44 on main
functional-head: fe962816 (saturated-call current-step admission, ranked staging, matcher/closure entry, hereditary result ABI, and caller-core pop)
contract-base: bc30ac44; accepted direct-call pointwise core and current compiler/runtime contracts
clean-at-update: true
slice: Exactly saturated closure calls now cross the pointwise core without whole-callee evaluation. State-indexed admission classifies the current call, zero-target staging strictly decreases compiler rank, matcher/closure consumption reconstructs the generated callee core while pushing the fused caller resource/result-ABI frame, and matcher-label pop restores the caller core.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof relation and roadmap only
checks: PASS Lean Beam update/sync/save (0 errors, 3 linter warnings); PASS direct lake build FirTalos.ConcreteStructuredSimulation (3110 jobs); PASS git diff --check; PASS make check (122 unit tests, 662 unique validation cases, 1968/1968 comparisons); PASS make talos-setup; PASS make talos-check (3133 jobs), repeated after rebase onto current main
bug-cards: none
blockers: none
handoff: ready for integration owner; branch is clean and rebased on main at bc30ac44
next: Define the relation-wide one-source-step classifier/advance theorem over the pointwise core, attaching fresh local admission only after each dynamic successor is known.
```
