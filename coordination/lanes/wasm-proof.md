# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 631fe8e1, current main including the accepted upstream Array.set! alignment
functional-head: 2cf613c7
contract-base: 913c2552, accepted W7 reduction-visible production decrement-body surface; rebased through current main 631fe8e1 with unchanged resident release ABI, layout, helper bodies, and proof-visible staged builders
clean-at-update: true
slice: Rebased the production last-reference adapter onto current main and factored the generated owned-object dispatcher through a reusable four-instruction kind-test theorem. Successful generation and adaptation now expose the exact release-header prefix and the exact constructor, closure-descriptor, and opaque branch composition. Recursive owned-child calls resolve through the real installed fir_dec_once index, guarded child frontiers adapt by induction over arbitrary index lists, and the production 32-field constructor branch adapts exactly to constructorReleaseProgram without normalizing 32 duplicated cases.
files: integration/talos/FirTalos/ConcreteResidentRelease.lean; coordination/lanes/wasm-proof.md
contracts: No source semantics, runtime operation, resident helper signature, semantic ABI, concrete layout, symbolic Wasm surface, emitter, executable behavior, or shared adapter contract changed. The new surfaces are proof-only consequences of successful generation, adaptation, and installation; no certificate or trusted premise was added.
checks: On current main 631fe8e1, Lean Beam refresh/save passed ConcreteResidentRelease.lean with zero diagnostics; targeted `lake build +FirTalos.ConcreteResidentRelease` passed all 3,079 jobs; `git diff --check` passed; `make check` passed with 726 unique cases, 2,160/2,160 comparisons equal, zero findings, 9,077 machine steps, 201 active bug cards, and 26 mailbox tests; `make talos-check` passed all 3,172 jobs.
bug-cards: FIR-BUG-wasm-none-adapter-if-branch-depth (existing confirmed shared-adapter bug; unchanged)
blockers: The constructor arm is unblocked. Exact adapter provenance for the resident Array loop remains blocked by FIR-BUG-wasm-none-adapter-if-branch-depth because the production encoder emits br 1 under if while the Talos adapter emits br 0. This checkpoint does not weaken or work around that contract.
handoff: GREEN LIGHT. Integration may fast-forward current main 631fe8e1 through functional head 2cf613c7 and this containing mailbox commit. The stack includes the exact production last-reference prefix, compositional owned dispatcher, recursive child-call adapter, and exact constructor branch adapter.
next: After landing, rebase wasm/talos-runtime onto the new main. Adapt descriptor-filtered closure captures by reusing instructions_releaseChild, then lift the exact constructor and closure branches through DecrementOnceInstallation. Coordinate the existing shared if-label depth repair before claiming adapter provenance for the Array arm.
```
