# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: d1994587, current main after accepted ElimDead Array proof recovery
functional-head: c99cd805
contract-base: d1994587; includes W7's proof-visible production decrementOnceFunction and releaseHeaderFunction surfaces, with unchanged resident helper ABI, layout, and executable bodies
clean-at-update: true
slice: Complete resident decrement/release refinement stack. Admission proves tagged values, erased zero, and rejected misaligned words before unsafe access; ordinary persistent, shared-count, zero-count underflow, and last-reference paths are separated. The exact seven-store release-header callee refines canonical header release. Recursive child traversal preserves the live-heap relation, resident memory, canonical mapped headers, and mapped payload frames. Constructor fields, closure captures selected by exact descriptor dispatch, and the logical live prefix of generic Arrays are released recursively. The Array specialization proves the exact binary-faithful decreasing loop and removes the caller-supplied opaque-body execution premise; spare capacity is excluded from the invariant.
files: integration/talos/FirTalos/ConcreteResidentRelease.lean; bugs/FIR-BUG-wasm-none-adapter-if-branch-depth.md; coordination/lanes/wasm-proof.md
contracts: No source semantics, runtime operation, resident helper signature, semantic ABI, concrete layout, symbolic Wasm surface, emitter, or executable behavior changed. W6 strengthens its proof-only ReleaseChildrenRun relation with the resident-memory size bound needed to exclude wasm32 cursor wrap. FIR-BUG-wasm-none-adapter-if-branch-depth records that the Talos proof adapter omits anonymous if-label depth; the production binary encoder is correct, and the exact Array theorem therefore uses the binary-faithful br 1 spelling without claiming current adapter provenance for that back-edge.
checks: Lean Beam update/sync/save passed with zero diagnostics for ConcreteResidentRelease.lean (source hash f6e10aec330f07e2). Forced `lake build +FirTalos.ConcreteResidentRelease` passed all 3,079 jobs before the source-preserving final rebase. After rebasing all 19 W6 commits onto main d1994587, `git diff --check` passed; `make check` passed with 726 unique cases, 2,160/2,160 comparisons equal, zero findings, 9,077 machine steps, 198 active bug cards, and 25 mailbox tests; `make talos-check` passed all 3,172 jobs.
bug-cards: FIR-BUG-wasm-none-adapter-if-branch-depth (confirmed shared proof-adapter mismatch; production binary encoder unaffected)
blockers: none for landing this exact release refinement checkpoint. A later shared-contract milestone must repair and propagate anonymous structured-control depth through the Talos adapter, CodeAdapted, active structured states, and suspended frames before the Array back-edge can inherit general symbolic-adapter provenance.
handoff: Integration may fast-forward the rebased cumulative W6 stack from main d1994587 through functional head c99cd805 and this containing mailbox commit. This gives W7 the requested proof checkpoint for ordinary shared decrement, last-reference release, and recursive constructor/closure/Array ownership while keeping the adapter discrepancy explicit.
next: After landing, rebase wasm/talos-runtime onto the new main. Then bind the exact recursive release cases into the production-installed whole-module theorem where the current adapter is sound, and queue the nested-if branch-depth repair as a separate shared proof-adapter contract change.
```
