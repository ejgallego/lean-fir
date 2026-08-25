# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 1c6aac49, current main including the accepted production last-reference and owned-dispatch constructor adapters
functional-head: ffc26250
contract-base: 913c2552, accepted W7 reduction-visible production decrement-body surface; rebased through current main 1c6aac49 with unchanged resident release ABI, layout, helper bodies, and proof-visible staged builders
clean-at-update: true
slice: Exposed the production closure-descriptor release adapter and its installed-body boundary. The proof factors direct and guarded recursive child-list adaptation, proves that the emitter's descriptor filter computes exactly closureOwnedCaptureIndices, and recursively adapts the checked ordinal/capture-count dispatch to closureDescriptorReleaseProgram. A generic local-equality dispatch theorem now proves the complete owned-release computation without branch-specific duplication. DecrementOnceInstallation.body_constructorClosure identifies the installed decrement body with exact constructor and closure semantics, leaving only the opaque/Array target existential; wp_body_of_constructorClosure lifts any suffix-insensitive semantic proof across that exact installed body.
files: integration/talos/FirTalos/ConcreteResidentRelease.lean; coordination/lanes/wasm-proof.md
contracts: No source semantics, runtime operation, resident helper signature, semantic ABI, concrete layout, symbolic Wasm surface, emitter, executable behavior, or shared adapter contract changed. The new surfaces are proof-only consequences of successful generation, adaptation, and installation; no certificate or trusted premise was added.
checks: On current main 1c6aac49, Lean Beam refresh/save passed ConcreteResidentRelease.lean with zero diagnostics; targeted `lake build +FirTalos.ConcreteResidentRelease` passed all 3,079 jobs; `git diff --check` passed; `make check` passed with 726 unique cases, 2,160/2,160 comparisons equal, zero findings, 9,077 machine steps, 202 active bug cards, and 26 mailbox tests; `make talos-check` passed all 3,172 jobs.
bug-cards: FIR-BUG-wasm-none-adapter-if-branch-depth (existing confirmed shared-adapter bug; unchanged)
blockers: Exact adapter provenance for the resident Array loop remains blocked by FIR-BUG-wasm-none-adapter-if-branch-depth because the production encoder emits br 1 under if while the Talos adapter emits br 0. This checkpoint does not weaken or work around that contract. Constructor and closure-descriptor installed-body provenance are unblocked.
handoff: GREEN LIGHT. Integration may fast-forward current main 1c6aac49 through functional head ffc26250 and this containing mailbox commit. The slice exposes exact production closure-descriptor adaptation and an installed decrement-body theorem with exact constructor and closure targets.
next: After landing, rebase wasm/talos-runtime onto the new main. Use wp_body_of_constructorClosure to lift the existing constructor and closure-descriptor refinement theorems through the installed decrement body and public call boundary. Coordinate the existing shared if-label depth repair before claiming adapter provenance for the Array arm.
```
